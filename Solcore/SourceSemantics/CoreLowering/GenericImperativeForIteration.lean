import Solcore.SourceSemantics.CoreLowering.GenericImperativeForConditions
import Solcore.SourceSemantics.CoreLowering.GenericImperativeForPost
import Solcore.SourceSemantics.CoreLowering.TypedImperativeForIteration

/-! Finite for iterations combine generic condition certificates with actual
body and post edges. The recursive statement theorem supplies both contracts;
no helper or child execution is stored in a static tree. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericImperativeFor
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedScopedStatements (Executes)
open TypedLexicalWhile (Scope ValuesContext Preserves FlowRep)
open TypedImperativeFor (LoopState Progress PostPreserves PostFaults body_preserves postValues)
open CompatibleExpressionPrimitives (bool_fields)
theorem iterations_success
    {program : Program} {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {post : List ForItemForm} {statements : List StatementId} {outcome : Dynamic.ControlOutcome}
    (trace : Dynamic.ForLoopExecutes program context evidence source environment before condition post statements finalContext outcome after) :
    ∀ {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope} {solved : List SolvedRequirement}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
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
      PostPreserves functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode →
      LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store →
      ∃ value finalStore finalMap finalWorld,
        Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
          (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  refine LoopStatements.for_induction
    (motive := fun context evidence source environment before condition post statements _ outcome after =>
      ∀ {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope} {solved : List SolvedRequirement}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
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
      PostPreserves functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode →
      LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store →
      ∃ value finalStore finalMap finalWorld,
        Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
          (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore) ?_ ?_ ?_ ?_ ?_ trace
  · intro context evidence source environment before after condition post statements conditionEvaluation
      certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults
      meaning conditionTree found valid unique agrees reference correct postCorrect state
    obtain ⟨value, nextStore, nextMap, nextWorld, evaluated, represented, progress⟩ :=
      condition_preserves functions program evidence meaning conditionTree found valid unique agrees state (.value conditionEvaluation)
    cases represented with
    | value payload =>
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      cases sameSource
      subst sameCore
      exact ⟨_, nextStore, nextMap, nextWorld, Core.LoopExecution.condition_false evaluated, .fallthrough environment, progress⟩
  · intro context evidence source environment before conditionHeap bodyHeap postHeap after condition post statements bodyFinalContext postFinalContext bodyEnvironment postEnvironment outcome
      conditionEvaluation bodyEvaluation postEvaluation next nextIH
      certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults
      meaning conditionTree found valid unique agrees reference correct postCorrect state
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
        have bodyTotal := conditionProgress.trans bodyProgress
        obtain ⟨postStore, postMap, postWorld, postEval, postProgress⟩ := postCorrect (state.progress bodyTotal) false postEvaluation
        have progress := bodyTotal.trans postProgress
        have nextState := state.progress progress
        obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress⟩ :=
          nextIH meaning conditionTree found valid unique agrees reference correct postCorrect nextState
        exact ⟨result, finalStore, finalMap, finalWorld,
          ForLoop.body_fallthrough conditionEval bodyEval
            (by simpa only [postValues, Bool.false_eq_true, ↓reduceIte, List.append_assoc, Core.LoopExecution.entryEnvironment, List.cons_append, List.nil_append] using postEval)
            nextState.selfRead nativeTrace, related, progress.trans finalProgress⟩
  · intro context evidence source environment before conditionHeap bodyHeap postHeap after condition post statements bodyFinalContext postFinalContext bodyEnvironment postEnvironment outcome
      conditionEvaluation bodyEvaluation postEvaluation next nextIH
      certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults
      meaning conditionTree found valid unique agrees reference correct postCorrect state
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
        have bodyTotal := conditionProgress.trans bodyProgress
        obtain ⟨postStore, postMap, postWorld, postEval, postProgress⟩ := postCorrect (state.progress bodyTotal) true postEvaluation
        have progress := bodyTotal.trans postProgress
        have nextState := state.progress progress
        obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress⟩ :=
          nextIH meaning conditionTree found valid unique agrees reference correct postCorrect nextState
        exact ⟨result, finalStore, finalMap, finalWorld,
          ForLoop.body_continuing conditionEval bodyEval
            (by simpa only [postValues, Bool.false_eq_true, ↓reduceIte, List.append_assoc, Core.LoopExecution.entryEnvironment, List.cons_append, List.nil_append] using postEval)
            nextState.selfRead nativeTrace, related, progress.trans finalProgress⟩
  · intro context evidence source environment before conditionHeap after condition post statements bodyFinalContext bodyEnvironment
      conditionEvaluation bodyEvaluation
      certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults
      meaning conditionTree found valid unique agrees reference correct postCorrect state
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
        exact ⟨_, bodyStore, bodyMap, bodyWorld, Core.LoopExecution.body_breaking conditionEval bodyEval, .fallthrough environment, conditionProgress.trans bodyProgress⟩
  · intro context evidence source environment before conditionHeap after condition post statements bodyFinalContext returned
      conditionEvaluation bodyEvaluation
      certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults
      meaning conditionTree found valid unique agrees reference correct postCorrect state
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
        exact ⟨_, bodyStore, bodyMap, bodyWorld, Core.LoopExecution.body_returned conditionEval bodyEval, .returned payload, conditionProgress.trans bodyProgress⟩


/-- Internal structural contract supplied by the concrete post header tree. -/
theorem iterations_fault
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {post : List ForItemForm} {statements : List StatementId} {reason : Dynamic.SemanticFault}
    (trace : Dynamic.ForLoopFaults program context evidence source environment before condition post statements reason after) :
    ∀ {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope} {solved : List SolvedRequirement}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
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
      PostPreserves functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode →
      PostFaults functions program evidence (source := source) (context := context) (scope := scope) (registry := registry) (faults := faults)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode →
      LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store →
      ∃ value finalStore finalMap finalWorld,
        Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
          (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type (.fault reason) value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  refine LoopStatements.for_fault_induction
    (motive := fun context evidence source environment before condition post statements reason after =>
      ∀ {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope} {solved : List SolvedRequirement}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
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
      PostPreserves functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode →
      PostFaults functions program evidence (source := source) (context := context) (scope := scope) (registry := registry) (faults := faults)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode →
      LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store →
      ∃ value finalStore finalMap finalWorld,
        Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
          (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type (.fault reason) value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore) ?_ ?_ ?_ ?_ ?_ ?_ ?_ trace
  · intro context evidence source environment before after condition post statements reason conditionFault
      certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults
      meaning conditionTree found valid unique agrees reference correct postCorrect postFailed state
    obtain ⟨value, nextStore, nextMap, nextWorld, evaluated, represented, progress⟩ :=
      condition_preserves functions program evidence meaning conditionTree found valid unique agrees state (.fault conditionFault)
    cases represented with
    | fault matched => exact ⟨_, nextStore, nextMap, nextWorld, Core.LoopExecution.condition_failure evaluated, .fault matched, progress⟩
  · intro context evidence source environment before after condition post statements value actualType conditionEvaluation notBoolean runtimeType
      certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults
      meaning conditionTree found valid unique agrees reference correct postCorrect postFailed state
    obtain ⟨value, nextStore, nextMap, nextWorld, evaluated, represented, progress⟩ :=
      condition_preserves functions program evidence meaning conditionTree found valid unique agrees state (.value conditionEvaluation)
    cases represented with
    | value payload =>
      obtain ⟨boolean, rfl, _⟩ := bool_fields payload
      exact False.elim (notBoolean trivial)
  · intro context evidence source environment before conditionHeap after condition post statements bodyContext reason conditionEvaluation bodyFault
      certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults
      meaning conditionTree found valid unique agrees reference correct postCorrect postFailed state
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
      | fault matched => exact ⟨_, bodyStore, bodyMap, bodyWorld, Core.LoopExecution.body_failure conditionEval bodyEval, .fault matched, conditionProgress.trans bodyProgress⟩
  · intro context evidence source environment before conditionHeap bodyHeap after condition post statements bodyFinalContext bodyEnvironment finalContext reason
      conditionEvaluation bodyEvaluation postEvaluation
      certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults
      meaning conditionTree found valid unique agrees reference correct postCorrect postFailed state
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
        have bodyTotal := conditionProgress.trans bodyProgress
        obtain ⟨token, postStore, postMap, postWorld, postEval, matched, postProgress⟩ :=
          postFailed (state.progress bodyTotal) false postEvaluation
        exact ⟨_, postStore, postMap, postWorld,
          ForLoop.body_fallthrough_post_fault conditionEval bodyEval
            (by simpa only [postValues, Bool.false_eq_true, ↓reduceIte, List.append_assoc, Core.LoopExecution.entryEnvironment, List.cons_append, List.nil_append] using postEval),
          .fault matched, bodyTotal.trans postProgress⟩
  · intro context evidence source environment before conditionHeap bodyHeap after condition post statements bodyFinalContext bodyEnvironment finalContext reason
      conditionEvaluation bodyEvaluation postEvaluation
      certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults
      meaning conditionTree found valid unique agrees reference correct postCorrect postFailed state
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
        have bodyTotal := conditionProgress.trans bodyProgress
        obtain ⟨token, postStore, postMap, postWorld, postEval, matched, postProgress⟩ :=
          postFailed (state.progress bodyTotal) true postEvaluation
        exact ⟨_, postStore, postMap, postWorld,
          ForLoop.body_continuing_post_fault conditionEval bodyEval
            (by simpa only [postValues, Bool.false_eq_true, ↓reduceIte, List.append_assoc, Core.LoopExecution.entryEnvironment, List.cons_append, List.nil_append] using postEval),
          .fault matched, bodyTotal.trans postProgress⟩
  · intro context evidence source environment before conditionHeap bodyHeap postHeap after condition post statements bodyFinalContext postFinalContext bodyEnvironment postEnvironment reason
      conditionEvaluation bodyEvaluation postEvaluation next nextIH
      certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults
      meaning conditionTree found valid unique agrees reference correct postCorrect postFailed state
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
        have bodyTotal := conditionProgress.trans bodyProgress
        obtain ⟨postStore, postMap, postWorld, postEval, postProgress⟩ := postCorrect (state.progress bodyTotal) false postEvaluation
        have progress := bodyTotal.trans postProgress
        have nextState := state.progress progress
        obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress⟩ :=
          nextIH meaning conditionTree found valid unique agrees reference correct postCorrect postFailed nextState
        exact ⟨result, finalStore, finalMap, finalWorld,
          ForLoop.body_fallthrough conditionEval bodyEval
            (by simpa only [postValues, Bool.false_eq_true, ↓reduceIte, List.append_assoc, Core.LoopExecution.entryEnvironment, List.cons_append, List.nil_append] using postEval)
            nextState.selfRead nativeTrace, related, progress.trans finalProgress⟩
  · intro context evidence source environment before conditionHeap bodyHeap postHeap after condition post statements bodyFinalContext postFinalContext bodyEnvironment postEnvironment reason
      conditionEvaluation bodyEvaluation postEvaluation next nextIH
      certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults
      meaning conditionTree found valid unique agrees reference correct postCorrect postFailed state
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
        have bodyTotal := conditionProgress.trans bodyProgress
        obtain ⟨postStore, postMap, postWorld, postEval, postProgress⟩ := postCorrect (state.progress bodyTotal) true postEvaluation
        have progress := bodyTotal.trans postProgress
        have nextState := state.progress progress
        obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress⟩ :=
          nextIH meaning conditionTree found valid unique agrees reference correct postCorrect postFailed nextState
        exact ⟨result, finalStore, finalMap, finalWorld,
          ForLoop.body_continuing conditionEval bodyEval
            (by simpa only [postValues, Bool.false_eq_true, ↓reduceIte, List.append_assoc, Core.LoopExecution.entryEnvironment, List.cons_append, List.nil_append] using postEval)
            nextState.selfRead nativeTrace, related, progress.trans finalProgress⟩

end Solcore.SourceSemantics.CoreLowering.GenericImperativeFor
