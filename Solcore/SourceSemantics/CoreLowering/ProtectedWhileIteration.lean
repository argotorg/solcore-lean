import Solcore.SourceSemantics.CoreLowering.ProtectedWhileBodyEdges

/-! Finite source while derivations run under the actual installed self-cell.
Each evaluated condition and lexical body retains the protected entry through
its observed heap, world and administrative progress. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedWhile
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext Progress FlowRep)
open CompatibleExpressionPrimitives (bool_fields)

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
      ProtectedLexicalAssignments.ControlAt.Preserves functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
        (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) false statements expected type code →
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason mapping world before store →
      ∃ value finalStore finalMap finalWorld,
        Core.LoopExecution.WhileTrace type (conditionCode.rename ξ) (code.rename ξ) selfReason location actual store value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  refine LoopStatements.while_induction
    (motive := fun context evidence source environment before condition statements _ outcome after =>
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
      ProtectedLexicalAssignments.ControlAt.Preserves functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
        (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) false statements expected type code →
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason mapping world before store →
      ∃ value finalStore finalMap finalWorld,
        Core.LoopExecution.WhileTrace type (conditionCode.rename ξ) (code.rename ξ) selfReason location actual store value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore) ?_ ?_ ?_ ?_ ?_ trace
  · intro context evidence source environment before after condition statements conditionEvaluation
      entry certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code selfReason mapping world store node faults
      transport meaning conditionTree found valid unique agrees reference correct state
    obtain ⟨value, nextStore, nextMap, nextWorld, evaluated, represented, progress, _⟩ :=
      condition_preserves functions program evidence transport meaning conditionTree found agrees state (.value conditionEvaluation)
    cases represented with
    | value payload =>
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      cases sameSource
      subst sameCore
      exact ⟨_, nextStore, nextMap, nextWorld, .done evaluated, .fallthrough environment, progress⟩
  · intro context evidence source environment before conditionHeap bodyHeap after condition statements bodyFinalContext bodyEnvironment outcome
      conditionEvaluation bodyEvaluation next nextIH
      entry certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code selfReason mapping world store node faults
      transport meaning conditionTree found valid unique agrees reference correct state
    obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress, _⟩ :=
      condition_preserves functions program evidence transport meaning conditionTree found agrees state (.value conditionEvaluation)
    cases conditionRelated with
    | value payload =>
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      cases sameSource
      subst sameCore
      obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress, _, _⟩ :=
        body_preserves functions program evidence transport correct valid agrees reference (state.advance transport conditionProgress) (.control bodyEvaluation)
      cases bodyRelated with
      | fallthrough _ =>
        have progress := conditionProgress.trans bodyProgress
        have nextState := state.advance transport progress
        obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress⟩ :=
          nextIH transport meaning conditionTree found valid unique agrees reference correct nextState
        exact ⟨result, finalStore, finalMap, finalWorld,
          .nextFallthrough conditionEval bodyEval nextState.1.selfRead nativeTrace, related, progress.trans finalProgress⟩
  · intro context evidence source environment before conditionHeap bodyHeap after condition statements bodyFinalContext bodyEnvironment outcome
      conditionEvaluation bodyEvaluation next nextIH
      entry certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code selfReason mapping world store node faults
      transport meaning conditionTree found valid unique agrees reference correct state
    obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress, _⟩ :=
      condition_preserves functions program evidence transport meaning conditionTree found agrees state (.value conditionEvaluation)
    cases conditionRelated with
    | value payload =>
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      cases sameSource
      subst sameCore
      obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress, _, _⟩ :=
        body_preserves functions program evidence transport correct valid agrees reference (state.advance transport conditionProgress) (.control bodyEvaluation)
      cases bodyRelated with
      | continuing _ =>
        have progress := conditionProgress.trans bodyProgress
        have nextState := state.advance transport progress
        obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress⟩ :=
          nextIH transport meaning conditionTree found valid unique agrees reference correct nextState
        exact ⟨result, finalStore, finalMap, finalWorld,
          .nextContinue conditionEval bodyEval nextState.1.selfRead nativeTrace, related, progress.trans finalProgress⟩
  · intro context evidence source environment before conditionHeap after condition statements bodyFinalContext bodyEnvironment
      conditionEvaluation bodyEvaluation
      entry certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code selfReason mapping world store node faults
      transport meaning conditionTree found valid unique agrees reference correct state
    obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress, _⟩ :=
      condition_preserves functions program evidence transport meaning conditionTree found agrees state (.value conditionEvaluation)
    cases conditionRelated with
    | value payload =>
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      cases sameSource
      subst sameCore
      obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress, _, _⟩ :=
        body_preserves functions program evidence transport correct valid agrees reference (state.advance transport conditionProgress) (.control bodyEvaluation)
      cases bodyRelated with
      | breaking _ =>
        exact ⟨_, bodyStore, bodyMap, bodyWorld, .breaks conditionEval bodyEval, .fallthrough environment, conditionProgress.trans bodyProgress⟩
  · intro context evidence source environment before conditionHeap after condition statements bodyFinalContext returned
      conditionEvaluation bodyEvaluation
      entry certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code selfReason mapping world store node faults
      transport meaning conditionTree found valid unique agrees reference correct state
    obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress, _⟩ :=
      condition_preserves functions program evidence transport meaning conditionTree found agrees state (.value conditionEvaluation)
    cases conditionRelated with
    | value payload =>
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      cases sameSource
      subst sameCore
      obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress, _, _⟩ :=
        body_preserves functions program evidence transport correct valid agrees reference (state.advance transport conditionProgress) (.control bodyEvaluation)
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
      ProtectedLexicalAssignments.ControlAt.Preserves functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
        (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) false statements expected type code →
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason mapping world before store →
      ∃ value finalStore finalMap finalWorld,
        Core.LoopExecution.WhileTrace type (conditionCode.rename ξ) (code.rename ξ) selfReason location actual store value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type (.fault reason) value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  refine LoopStatements.while_fault_induction
    (motive := fun context evidence source environment before condition statements reason after =>
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
      ProtectedLexicalAssignments.ControlAt.Preserves functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
        (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) false statements expected type code →
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason mapping world before store →
      ∃ value finalStore finalMap finalWorld,
        Core.LoopExecution.WhileTrace type (conditionCode.rename ξ) (code.rename ξ) selfReason location actual store value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type (.fault reason) value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore) ?_ ?_ ?_ ?_ ?_ trace
  · intro context evidence source environment before after condition statements reason conditionFault
      entry certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code selfReason mapping world store node faults
      transport meaning conditionTree found valid unique agrees reference correct state
    obtain ⟨value, nextStore, nextMap, nextWorld, evaluated, represented, progress, _⟩ :=
      condition_preserves functions program evidence transport meaning conditionTree found agrees state (.fault conditionFault)
    cases represented with
    | fault matched => exact ⟨_, nextStore, nextMap, nextWorld, .conditionFault evaluated, .fault matched, progress⟩
  · intro context evidence source environment before after condition statements value actualType conditionEvaluation notBoolean runtimeType
      entry certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code selfReason mapping world store node faults
      transport meaning conditionTree found valid unique agrees reference correct state
    obtain ⟨value, nextStore, nextMap, nextWorld, evaluated, represented, progress, _⟩ :=
      condition_preserves functions program evidence transport meaning conditionTree found agrees state (.value conditionEvaluation)
    cases represented with
    | value payload =>
      obtain ⟨boolean, rfl, _⟩ := bool_fields payload
      exact False.elim (notBoolean trivial)
  · intro context evidence source environment before conditionHeap after condition statements bodyContext reason conditionEvaluation bodyFault
      entry certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code selfReason mapping world store node faults
      transport meaning conditionTree found valid unique agrees reference correct state
    obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress, _⟩ :=
      condition_preserves functions program evidence transport meaning conditionTree found agrees state (.value conditionEvaluation)
    cases conditionRelated with
    | value payload =>
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      cases sameSource
      subst sameCore
      obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress, _, _⟩ :=
        body_preserves functions program evidence transport correct valid agrees reference (state.advance transport conditionProgress) (.fault bodyFault)
      cases bodyRelated with
      | fault matched => exact ⟨_, bodyStore, bodyMap, bodyWorld, .bodyFault conditionEval bodyEval, .fault matched, conditionProgress.trans bodyProgress⟩
  · intro context evidence source environment before conditionHeap bodyHeap after condition statements bodyFinalContext bodyEnvironment reason
      conditionEvaluation bodyEvaluation next nextIH
      entry certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code selfReason mapping world store node faults
      transport meaning conditionTree found valid unique agrees reference correct state
    obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress, _⟩ :=
      condition_preserves functions program evidence transport meaning conditionTree found agrees state (.value conditionEvaluation)
    cases conditionRelated with
    | value payload =>
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      cases sameSource
      subst sameCore
      obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress, _, _⟩ :=
        body_preserves functions program evidence transport correct valid agrees reference (state.advance transport conditionProgress) (.control bodyEvaluation)
      cases bodyRelated with
      | fallthrough _ =>
        have progress := conditionProgress.trans bodyProgress
        have nextState := state.advance transport progress
        obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress⟩ :=
          nextIH transport meaning conditionTree found valid unique agrees reference correct nextState
        exact ⟨result, finalStore, finalMap, finalWorld,
          .nextFallthrough conditionEval bodyEval nextState.1.selfRead nativeTrace, related, progress.trans finalProgress⟩
  · intro context evidence source environment before conditionHeap bodyHeap after condition statements bodyFinalContext bodyEnvironment reason
      conditionEvaluation bodyEvaluation next nextIH
      entry certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code selfReason mapping world store node faults
      transport meaning conditionTree found valid unique agrees reference correct state
    obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress, _⟩ :=
      condition_preserves functions program evidence transport meaning conditionTree found agrees state (.value conditionEvaluation)
    cases conditionRelated with
    | value payload =>
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      cases sameSource
      subst sameCore
      obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress, _, _⟩ :=
        body_preserves functions program evidence transport correct valid agrees reference (state.advance transport conditionProgress) (.control bodyEvaluation)
      cases bodyRelated with
      | continuing _ =>
        have progress := conditionProgress.trans bodyProgress
        have nextState := state.advance transport progress
        obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress⟩ :=
          nextIH transport meaning conditionTree found valid unique agrees reference correct nextState
        exact ⟨result, finalStore, finalMap, finalWorld,
          .nextContinue conditionEval bodyEval nextState.1.selfRead nativeTrace, related, progress.trans finalProgress⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedWhile
