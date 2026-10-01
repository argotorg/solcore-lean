import Solcore.SourceSemantics.CoreLowering.TypedLexicalWhileIteration

/-! Condition certificates run under the real Unit/self-cell prefix. The
installed closure, administrative reads and common heap are the existing loop
state; arbitrary captured values stay typed in the actual ambient definitions. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericImperativeWhile
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext)
open TypedLexicalWhile (LoopState Progress Preserves FlowRep body_preserves)
open CompatibleExpressionPrimitives (bool_fields)
variable {readFuel : Nat} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {contextLocation location : Location} {type : Ty} {conditionCode body : Expr} {selfReason : Word}

variable {scope : Scope} {mapping : LocationMap} {world : StoreTyping}
  {before after : Dynamic.Heap} {store : Store}
variable (functions) (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {certificate : GenericExpressionMeaning.Certificate}
  (meaning : TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    program context evidence source certificate faults)
  (reflection : TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    program context evidence source certificate faults)

include meaning in
theorem condition_preserves {condition : ExpressionId} {node : ExpressionNode}
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (_valid : CompatibleExpressionLiterals.ContextValid solved context evidence) (_unique : NodeOccurrencesUnique source)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type (conditionCode.rename ξ) body selfReason mapping world before store)
    {outcome : Dynamic.ExpressionOutcome}
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before condition outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
        (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  have actualAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)) canonical
      (Core.LoopExecution.entryEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related, heaps, maps, worlds, frame, metadata⟩ :=
    meaning tree found
      state.environments state.heaps state.locals actualAgrees (.cons .unit (.cons (.cellRef state.selfTyped) state.actualTyped)) trace
  exact ⟨value, finalStore, finalMap, finalWorld,
    by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.conditionCode, Core.LoopExecution.entryEnvironment] using evaluated,
    related, heaps, maps, worlds, frame, metadata⟩

include reflection in
theorem condition_reflects {condition : ExpressionId} {node : ExpressionNode}
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (_valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type (conditionCode.rename ξ) body selfReason mapping world before store)
    {value : Value} {finalStore : Store}
    (evaluated : Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
      (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before condition outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  have actualAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)) canonical
      (Core.LoopExecution.entryEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit
  obtain ⟨outcome, after, finalMap, finalWorld, trace, related, heaps, maps, worlds, frame, metadata⟩ :=
    reflection tree found
      state.environments state.heaps state.locals actualAgrees (.cons .unit (.cons (.cellRef state.selfTyped) state.actualTyped))
      (by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.conditionCode, Core.LoopExecution.entryEnvironment] using evaluated)
  exact ⟨outcome, after, finalMap, finalWorld, trace, related, heaps, maps, worlds, frame, metadata⟩


theorem iterations_success
    {program : Program} {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {statements : List StatementId} {outcome : Dynamic.ControlOutcome}
    (trace : Dynamic.WhileExecutes program context evidence source environment before condition statements finalContext outcome after) :
    ∀ {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope} {solved : List SolvedRequirement}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {faults : FunctionCalls.FaultRep},
      TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source certificate faults →
      certificate scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      CompatibleExpressionLiterals.ContextValid solved context evidence → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      Preserves functions program evidence (source := source) (context := context) (registry := registry)
        (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) false statements expected type code →
      LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason mapping world before store →
      ∃ value finalStore finalMap finalWorld,
        Core.LoopExecution.WhileTrace type (conditionCode.rename ξ) (code.rename ξ) selfReason location actual store value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  refine LoopStatements.while_induction
    (motive := fun context evidence source environment before condition statements _ outcome after =>
      ∀ {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope} {solved : List SolvedRequirement}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {faults : FunctionCalls.FaultRep},
      TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source certificate faults →
      certificate scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      CompatibleExpressionLiterals.ContextValid solved context evidence → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      Preserves functions program evidence (source := source) (context := context) (registry := registry)
        (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) false statements expected type code →
      LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason mapping world before store →
      ∃ value finalStore finalMap finalWorld,
        Core.LoopExecution.WhileTrace type (conditionCode.rename ξ) (code.rename ξ) selfReason location actual store value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore) ?_ ?_ ?_ ?_ ?_ trace
  · intro context evidence source environment before after condition statements conditionEvaluation
      certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code selfReason mapping world store node faults
      meaning conditionTree found valid unique agrees reference correct state
    obtain ⟨value, nextStore, nextMap, nextWorld, evaluated, represented, progress⟩ :=
      condition_preserves functions program evidence meaning conditionTree found valid unique agrees state (.value conditionEvaluation)
    cases represented with
    | value payload =>
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      cases sameSource
      subst sameCore
      exact ⟨_, nextStore, nextMap, nextWorld, .done evaluated, .fallthrough environment, progress⟩
  · intro context evidence source environment before conditionHeap bodyHeap after condition statements bodyFinalContext bodyEnvironment outcome
      conditionEvaluation bodyEvaluation next nextIH
      certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code selfReason mapping world store node faults
      meaning conditionTree found valid unique agrees reference correct state
    obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress⟩ :=
      condition_preserves functions program evidence meaning conditionTree found valid unique agrees state (.value conditionEvaluation)
    cases conditionRelated with
    | value payload =>
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      cases sameSource
      subst sameCore
      obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress⟩ :=
        body_preserves functions program evidence correct valid agrees reference (state.progress conditionProgress) (.control bodyEvaluation)
      cases bodyRelated with
      | fallthrough _ =>
        have progress := conditionProgress.trans bodyProgress
        have nextState := state.progress progress
        obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress⟩ :=
          nextIH meaning conditionTree found valid unique agrees reference correct nextState
        exact ⟨result, finalStore, finalMap, finalWorld,
          .nextFallthrough conditionEval bodyEval nextState.selfRead nativeTrace, related, progress.trans finalProgress⟩
  · intro context evidence source environment before conditionHeap bodyHeap after condition statements bodyFinalContext bodyEnvironment outcome
      conditionEvaluation bodyEvaluation next nextIH
      certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code selfReason mapping world store node faults
      meaning conditionTree found valid unique agrees reference correct state
    obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress⟩ :=
      condition_preserves functions program evidence meaning conditionTree found valid unique agrees state (.value conditionEvaluation)
    cases conditionRelated with
    | value payload =>
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      cases sameSource
      subst sameCore
      obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress⟩ :=
        body_preserves functions program evidence correct valid agrees reference (state.progress conditionProgress) (.control bodyEvaluation)
      cases bodyRelated with
      | continuing _ =>
        have progress := conditionProgress.trans bodyProgress
        have nextState := state.progress progress
        obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress⟩ :=
          nextIH meaning conditionTree found valid unique agrees reference correct nextState
        exact ⟨result, finalStore, finalMap, finalWorld,
          .nextContinue conditionEval bodyEval nextState.selfRead nativeTrace, related, progress.trans finalProgress⟩
  · intro context evidence source environment before conditionHeap after condition statements bodyFinalContext bodyEnvironment
      conditionEvaluation bodyEvaluation
      certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code selfReason mapping world store node faults
      meaning conditionTree found valid unique agrees reference correct state
    obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress⟩ :=
      condition_preserves functions program evidence meaning conditionTree found valid unique agrees state (.value conditionEvaluation)
    cases conditionRelated with
    | value payload =>
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      cases sameSource
      subst sameCore
      obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress⟩ :=
        body_preserves functions program evidence correct valid agrees reference (state.progress conditionProgress) (.control bodyEvaluation)
      cases bodyRelated with
      | breaking _ =>
        exact ⟨_, bodyStore, bodyMap, bodyWorld, .breaks conditionEval bodyEval, .fallthrough environment, conditionProgress.trans bodyProgress⟩
  · intro context evidence source environment before conditionHeap after condition statements bodyFinalContext returned
      conditionEvaluation bodyEvaluation
      certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code selfReason mapping world store node faults
      meaning conditionTree found valid unique agrees reference correct state
    obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress⟩ :=
      condition_preserves functions program evidence meaning conditionTree found valid unique agrees state (.value conditionEvaluation)
    cases conditionRelated with
    | value payload =>
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      cases sameSource
      subst sameCore
      obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress⟩ :=
        body_preserves functions program evidence correct valid agrees reference (state.progress conditionProgress) (.control bodyEvaluation)
      cases bodyRelated with
      | returned payload =>
        exact ⟨_, bodyStore, bodyMap, bodyWorld, .returns conditionEval bodyEval, .returned payload, conditionProgress.trans bodyProgress⟩

/-- Source faults preserve all earlier iterations and condition effects. The
static Bool condition rules out the independent wrong-condition-type branch. -/
theorem iterations_fault
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {statements : List StatementId} {reason : Dynamic.SemanticFault}
    (trace : Dynamic.WhileFaults program context evidence source environment before condition statements reason after) :
    ∀ {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope} {solved : List SolvedRequirement}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {faults : FunctionCalls.FaultRep},
      TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source certificate faults →
      certificate scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      CompatibleExpressionLiterals.ContextValid solved context evidence → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      Preserves functions program evidence (source := source) (context := context) (registry := registry)
        (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) false statements expected type code →
      LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason mapping world before store →
      ∃ value finalStore finalMap finalWorld,
        Core.LoopExecution.WhileTrace type (conditionCode.rename ξ) (code.rename ξ) selfReason location actual store value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type (.fault reason) value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  refine LoopStatements.while_fault_induction
    (motive := fun context evidence source environment before condition statements reason after =>
      ∀ {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope} {solved : List SolvedRequirement}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {faults : FunctionCalls.FaultRep},
      TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source certificate faults →
      certificate scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      CompatibleExpressionLiterals.ContextValid solved context evidence → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      Preserves functions program evidence (source := source) (context := context) (registry := registry)
        (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) false statements expected type code →
      LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason mapping world before store →
      ∃ value finalStore finalMap finalWorld,
        Core.LoopExecution.WhileTrace type (conditionCode.rename ξ) (code.rename ξ) selfReason location actual store value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type (.fault reason) value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore) ?_ ?_ ?_ ?_ ?_ trace
  · intro context evidence source environment before after condition statements reason conditionFault
      certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code selfReason mapping world store node faults
      meaning conditionTree found valid unique agrees reference correct state
    obtain ⟨value, nextStore, nextMap, nextWorld, evaluated, represented, progress⟩ :=
      condition_preserves functions program evidence meaning conditionTree found valid unique agrees state (.fault conditionFault)
    cases represented with
    | fault matched => exact ⟨_, nextStore, nextMap, nextWorld, .conditionFault evaluated, .fault matched, progress⟩
  · intro context evidence source environment before after condition statements value actualType conditionEvaluation notBoolean runtimeType
      certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code selfReason mapping world store node faults
      meaning conditionTree found valid unique agrees reference correct state
    obtain ⟨value, nextStore, nextMap, nextWorld, evaluated, represented, progress⟩ :=
      condition_preserves functions program evidence meaning conditionTree found valid unique agrees state (.value conditionEvaluation)
    cases represented with
    | value payload =>
      obtain ⟨boolean, rfl, _⟩ := bool_fields payload
      exact False.elim (notBoolean trivial)
  · intro context evidence source environment before conditionHeap after condition statements bodyContext reason conditionEvaluation bodyFault
      certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code selfReason mapping world store node faults
      meaning conditionTree found valid unique agrees reference correct state
    obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress⟩ :=
      condition_preserves functions program evidence meaning conditionTree found valid unique agrees state (.value conditionEvaluation)
    cases conditionRelated with
    | value payload =>
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      cases sameSource
      subst sameCore
      obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress⟩ :=
        body_preserves functions program evidence correct valid agrees reference (state.progress conditionProgress) (.fault bodyFault)
      cases bodyRelated with
      | fault matched => exact ⟨_, bodyStore, bodyMap, bodyWorld, .bodyFault conditionEval bodyEval, .fault matched, conditionProgress.trans bodyProgress⟩
  · intro context evidence source environment before conditionHeap bodyHeap after condition statements bodyFinalContext bodyEnvironment reason
      conditionEvaluation bodyEvaluation next nextIH
      certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code selfReason mapping world store node faults
      meaning conditionTree found valid unique agrees reference correct state
    obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress⟩ :=
      condition_preserves functions program evidence meaning conditionTree found valid unique agrees state (.value conditionEvaluation)
    cases conditionRelated with
    | value payload =>
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      cases sameSource
      subst sameCore
      obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress⟩ :=
        body_preserves functions program evidence correct valid agrees reference (state.progress conditionProgress) (.control bodyEvaluation)
      cases bodyRelated with
      | fallthrough _ =>
        have progress := conditionProgress.trans bodyProgress
        have nextState := state.progress progress
        obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress⟩ :=
          nextIH meaning conditionTree found valid unique agrees reference correct nextState
        exact ⟨result, finalStore, finalMap, finalWorld,
          .nextFallthrough conditionEval bodyEval nextState.selfRead nativeTrace, related, progress.trans finalProgress⟩
  · intro context evidence source environment before conditionHeap bodyHeap after condition statements bodyFinalContext bodyEnvironment reason
      conditionEvaluation bodyEvaluation next nextIH
      certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code selfReason mapping world store node faults
      meaning conditionTree found valid unique agrees reference correct state
    obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress⟩ :=
      condition_preserves functions program evidence meaning conditionTree found valid unique agrees state (.value conditionEvaluation)
    cases conditionRelated with
    | value payload =>
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      cases sameSource
      subst sameCore
      obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress⟩ :=
        body_preserves functions program evidence correct valid agrees reference (state.progress conditionProgress) (.control bodyEvaluation)
      cases bodyRelated with
      | continuing _ =>
        have progress := conditionProgress.trans bodyProgress
        have nextState := state.progress progress
        obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress⟩ :=
          nextIH meaning conditionTree found valid unique agrees reference correct nextState
        exact ⟨result, finalStore, finalMap, finalWorld,
          .nextContinue conditionEval bodyEval nextState.selfRead nativeTrace, related, progress.trans finalProgress⟩

end Solcore.SourceSemantics.CoreLowering.GenericImperativeWhile
