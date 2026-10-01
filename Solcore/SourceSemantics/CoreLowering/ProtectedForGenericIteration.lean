import Solcore.SourceSemantics.CoreLowering.ProtectedForBodyContracts
import Solcore.SourceSemantics.CoreLowering.ForSourceInduction

/-! Finite for iterations combine generic condition certificates with actual
body and post edges. The recursive statement theorem supplies both contracts;
no helper or child execution is stored in a static tree. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedFor.Body
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedScopedStatements (Executes)
open TypedLexicalWhile (Scope ValuesContext FlowRep)
open ProtectedWhile.Body (Preserves)
open TypedImperativeFor (Progress postValues)
open CompatibleExpressionPrimitives (bool_fields)
theorem iterations_success
    {program : Program} {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {post : List ForItemForm} {statements : List StatementId} {outcome : Dynamic.ControlOutcome}
    (trace : Dynamic.ForLoopExecutes program context evidence source environment before condition post statements finalContext outcome after) :
    ∀ {entry : ProtectedExpressionMeaning.Entry} {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope} {solved : List SolvedRequirement}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {faults : FunctionCalls.FaultRep},
      ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source certificate faults entry →
      ProtectedExpressionMeaning.Transport entry →
      certificate scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      CompatibleExpressionLiterals.ContextValid solved context evidence → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      Preserves functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
        (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) false statements expected type code →
      PostPreserves functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode →
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store →
      ∃ value finalStore finalMap finalWorld,
        Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
          (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  refine LoopStatements.for_induction
    (motive := fun context evidence source environment before condition post statements _ outcome after =>
      ∀ {entry : ProtectedExpressionMeaning.Entry} {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope} {solved : List SolvedRequirement}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {faults : FunctionCalls.FaultRep},
      ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source certificate faults entry →
      ProtectedExpressionMeaning.Transport entry →
      certificate scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      CompatibleExpressionLiterals.ContextValid solved context evidence → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      Preserves functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
        (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) false statements expected type code →
      PostPreserves functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode →
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store →
      ∃ value finalStore finalMap finalWorld,
        Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
          (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore) ?_ ?_ ?_ ?_ ?_ trace
  · intro context evidence source environment before after condition post statements conditionEvaluation
      entry certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults
      meaning transport conditionTree found valid unique agrees reference correct postCorrect state
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
      entry certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults
      meaning transport conditionTree found valid unique agrees reference correct postCorrect state
    obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress⟩ :=
      condition_preserves functions program evidence meaning conditionTree found valid unique agrees state (.value conditionEvaluation)
    cases conditionRelated with
    | value payload =>
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      cases sameSource
      subst sameCore
      obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress⟩ :=
        body_preserves functions program evidence correct valid agrees reference (state.advance transport conditionProgress) (.control bodyEvaluation)
      cases bodyRelated with
      | fallthrough _ =>
        have bodyTotal := conditionProgress.trans bodyProgress
        obtain ⟨postStore, postMap, postWorld, postEval, postProgress⟩ := postCorrect (state.advance transport bodyTotal) false postEvaluation
        have progress := bodyTotal.trans postProgress
        have nextState := state.advance transport progress
        obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress⟩ :=
          nextIH meaning transport conditionTree found valid unique agrees reference correct postCorrect nextState
        exact ⟨result, finalStore, finalMap, finalWorld,
          ForLoop.body_fallthrough conditionEval bodyEval
            (by simpa only [postValues, Bool.false_eq_true, ↓reduceIte, List.append_assoc, Core.LoopExecution.entryEnvironment, List.cons_append, List.nil_append] using postEval)
            nextState.1.selfRead nativeTrace, related, progress.trans finalProgress⟩
  · intro context evidence source environment before conditionHeap bodyHeap postHeap after condition post statements bodyFinalContext postFinalContext bodyEnvironment postEnvironment outcome
      conditionEvaluation bodyEvaluation postEvaluation next nextIH
      entry certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults
      meaning transport conditionTree found valid unique agrees reference correct postCorrect state
    obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress⟩ :=
      condition_preserves functions program evidence meaning conditionTree found valid unique agrees state (.value conditionEvaluation)
    cases conditionRelated with
    | value payload =>
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      cases sameSource
      subst sameCore
      obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress⟩ :=
        body_preserves functions program evidence correct valid agrees reference (state.advance transport conditionProgress) (.control bodyEvaluation)
      cases bodyRelated with
      | continuing _ =>
        have bodyTotal := conditionProgress.trans bodyProgress
        obtain ⟨postStore, postMap, postWorld, postEval, postProgress⟩ := postCorrect (state.advance transport bodyTotal) true postEvaluation
        have progress := bodyTotal.trans postProgress
        have nextState := state.advance transport progress
        obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress⟩ :=
          nextIH meaning transport conditionTree found valid unique agrees reference correct postCorrect nextState
        exact ⟨result, finalStore, finalMap, finalWorld,
          ForLoop.body_continuing conditionEval bodyEval
            (by simpa only [postValues, Bool.false_eq_true, ↓reduceIte, List.append_assoc, Core.LoopExecution.entryEnvironment, List.cons_append, List.nil_append] using postEval)
            nextState.1.selfRead nativeTrace, related, progress.trans finalProgress⟩
  · intro context evidence source environment before conditionHeap after condition post statements bodyFinalContext bodyEnvironment
      conditionEvaluation bodyEvaluation
      entry certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults
      meaning transport conditionTree found valid unique agrees reference correct postCorrect state
    obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress⟩ :=
      condition_preserves functions program evidence meaning conditionTree found valid unique agrees state (.value conditionEvaluation)
    cases conditionRelated with
    | value payload =>
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      cases sameSource
      subst sameCore
      obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress⟩ :=
        body_preserves functions program evidence correct valid agrees reference (state.advance transport conditionProgress) (.control bodyEvaluation)
      cases bodyRelated with
      | breaking _ =>
        exact ⟨_, bodyStore, bodyMap, bodyWorld, Core.LoopExecution.body_breaking conditionEval bodyEval, .fallthrough environment, conditionProgress.trans bodyProgress⟩
  · intro context evidence source environment before conditionHeap after condition post statements bodyFinalContext returned
      conditionEvaluation bodyEvaluation
      entry certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults
      meaning transport conditionTree found valid unique agrees reference correct postCorrect state
    obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress⟩ :=
      condition_preserves functions program evidence meaning conditionTree found valid unique agrees state (.value conditionEvaluation)
    cases conditionRelated with
    | value payload =>
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      cases sameSource
      subst sameCore
      obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress⟩ :=
        body_preserves functions program evidence correct valid agrees reference (state.advance transport conditionProgress) (.control bodyEvaluation)
      cases bodyRelated with
      | returned payload =>
        exact ⟨_, bodyStore, bodyMap, bodyWorld, Core.LoopExecution.body_returned conditionEval bodyEval, .returned payload, conditionProgress.trans bodyProgress⟩


/-- Internal structural contract supplied by the concrete post header tree. -/
theorem iterations_fault
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {post : List ForItemForm} {statements : List StatementId} {reason : Dynamic.SemanticFault}
    (trace : Dynamic.ForLoopFaults program context evidence source environment before condition post statements reason after) :
    ∀ {entry : ProtectedExpressionMeaning.Entry} {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope} {solved : List SolvedRequirement}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {faults : FunctionCalls.FaultRep},
      ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source certificate faults entry →
      ProtectedExpressionMeaning.Transport entry →
      certificate scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      CompatibleExpressionLiterals.ContextValid solved context evidence → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      Preserves functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
        (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) false statements expected type code →
      PostPreserves functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode →
      PostFaults functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry) (faults := faults)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode →
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store →
      ∃ value finalStore finalMap finalWorld,
        Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
          (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type (.fault reason) value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  refine LoopStatements.for_fault_induction
    (motive := fun context evidence source environment before condition post statements reason after =>
      ∀ {entry : ProtectedExpressionMeaning.Entry} {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope} {solved : List SolvedRequirement}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {faults : FunctionCalls.FaultRep},
      ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source certificate faults entry →
      ProtectedExpressionMeaning.Transport entry →
      certificate scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      CompatibleExpressionLiterals.ContextValid solved context evidence → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      Preserves functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
        (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) false statements expected type code →
      PostPreserves functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode →
      PostFaults functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry) (faults := faults)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode →
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store →
      ∃ value finalStore finalMap finalWorld,
        Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
          (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type (.fault reason) value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore) ?_ ?_ ?_ ?_ ?_ ?_ ?_ trace
  · intro context evidence source environment before after condition post statements reason conditionFault
      entry certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults
      meaning transport conditionTree found valid unique agrees reference correct postCorrect postFailed state
    obtain ⟨value, nextStore, nextMap, nextWorld, evaluated, represented, progress⟩ :=
      condition_preserves functions program evidence meaning conditionTree found valid unique agrees state (.fault conditionFault)
    cases represented with
    | fault matched => exact ⟨_, nextStore, nextMap, nextWorld, Core.LoopExecution.condition_failure evaluated, .fault matched, progress⟩
  · intro context evidence source environment before after condition post statements value actualType conditionEvaluation notBoolean runtimeType
      entry certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults
      meaning transport conditionTree found valid unique agrees reference correct postCorrect postFailed state
    obtain ⟨value, nextStore, nextMap, nextWorld, evaluated, represented, progress⟩ :=
      condition_preserves functions program evidence meaning conditionTree found valid unique agrees state (.value conditionEvaluation)
    cases represented with
    | value payload =>
      obtain ⟨boolean, rfl, _⟩ := bool_fields payload
      exact False.elim (notBoolean trivial)
  · intro context evidence source environment before conditionHeap after condition post statements bodyContext reason conditionEvaluation bodyFault
      entry certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults
      meaning transport conditionTree found valid unique agrees reference correct postCorrect postFailed state
    obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress⟩ :=
      condition_preserves functions program evidence meaning conditionTree found valid unique agrees state (.value conditionEvaluation)
    cases conditionRelated with
    | value payload =>
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      cases sameSource
      subst sameCore
      obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress⟩ :=
        body_preserves functions program evidence correct valid agrees reference (state.advance transport conditionProgress) (.fault bodyFault)
      cases bodyRelated with
      | fault matched => exact ⟨_, bodyStore, bodyMap, bodyWorld, Core.LoopExecution.body_failure conditionEval bodyEval, .fault matched, conditionProgress.trans bodyProgress⟩
  · intro context evidence source environment before conditionHeap bodyHeap after condition post statements bodyFinalContext bodyEnvironment finalContext reason
      conditionEvaluation bodyEvaluation postEvaluation
      entry certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults
      meaning transport conditionTree found valid unique agrees reference correct postCorrect postFailed state
    obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress⟩ :=
      condition_preserves functions program evidence meaning conditionTree found valid unique agrees state (.value conditionEvaluation)
    cases conditionRelated with
    | value payload =>
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      cases sameSource
      subst sameCore
      obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress⟩ :=
        body_preserves functions program evidence correct valid agrees reference (state.advance transport conditionProgress) (.control bodyEvaluation)
      cases bodyRelated with
      | fallthrough _ =>
        have bodyTotal := conditionProgress.trans bodyProgress
        obtain ⟨token, postStore, postMap, postWorld, postEval, matched, postProgress⟩ :=
          postFailed (state.advance transport bodyTotal) false postEvaluation
        exact ⟨_, postStore, postMap, postWorld,
          ForLoop.body_fallthrough_post_fault conditionEval bodyEval
            (by simpa only [postValues, Bool.false_eq_true, ↓reduceIte, List.append_assoc, Core.LoopExecution.entryEnvironment, List.cons_append, List.nil_append] using postEval),
          .fault matched, bodyTotal.trans postProgress⟩
  · intro context evidence source environment before conditionHeap bodyHeap after condition post statements bodyFinalContext bodyEnvironment finalContext reason
      conditionEvaluation bodyEvaluation postEvaluation
      entry certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults
      meaning transport conditionTree found valid unique agrees reference correct postCorrect postFailed state
    obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress⟩ :=
      condition_preserves functions program evidence meaning conditionTree found valid unique agrees state (.value conditionEvaluation)
    cases conditionRelated with
    | value payload =>
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      cases sameSource
      subst sameCore
      obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress⟩ :=
        body_preserves functions program evidence correct valid agrees reference (state.advance transport conditionProgress) (.control bodyEvaluation)
      cases bodyRelated with
      | continuing _ =>
        have bodyTotal := conditionProgress.trans bodyProgress
        obtain ⟨token, postStore, postMap, postWorld, postEval, matched, postProgress⟩ :=
          postFailed (state.advance transport bodyTotal) true postEvaluation
        exact ⟨_, postStore, postMap, postWorld,
          ForLoop.body_continuing_post_fault conditionEval bodyEval
            (by simpa only [postValues, Bool.false_eq_true, ↓reduceIte, List.append_assoc, Core.LoopExecution.entryEnvironment, List.cons_append, List.nil_append] using postEval),
          .fault matched, bodyTotal.trans postProgress⟩
  · intro context evidence source environment before conditionHeap bodyHeap postHeap after condition post statements bodyFinalContext postFinalContext bodyEnvironment postEnvironment reason
      conditionEvaluation bodyEvaluation postEvaluation next nextIH
      entry certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults
      meaning transport conditionTree found valid unique agrees reference correct postCorrect postFailed state
    obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress⟩ :=
      condition_preserves functions program evidence meaning conditionTree found valid unique agrees state (.value conditionEvaluation)
    cases conditionRelated with
    | value payload =>
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      cases sameSource
      subst sameCore
      obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress⟩ :=
        body_preserves functions program evidence correct valid agrees reference (state.advance transport conditionProgress) (.control bodyEvaluation)
      cases bodyRelated with
      | fallthrough _ =>
        have bodyTotal := conditionProgress.trans bodyProgress
        obtain ⟨postStore, postMap, postWorld, postEval, postProgress⟩ := postCorrect (state.advance transport bodyTotal) false postEvaluation
        have progress := bodyTotal.trans postProgress
        have nextState := state.advance transport progress
        obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress⟩ :=
          nextIH meaning transport conditionTree found valid unique agrees reference correct postCorrect postFailed nextState
        exact ⟨result, finalStore, finalMap, finalWorld,
          ForLoop.body_fallthrough conditionEval bodyEval
            (by simpa only [postValues, Bool.false_eq_true, ↓reduceIte, List.append_assoc, Core.LoopExecution.entryEnvironment, List.cons_append, List.nil_append] using postEval)
            nextState.1.selfRead nativeTrace, related, progress.trans finalProgress⟩
  · intro context evidence source environment before conditionHeap bodyHeap postHeap after condition post statements bodyFinalContext postFinalContext bodyEnvironment postEnvironment reason
      conditionEvaluation bodyEvaluation postEvaluation next nextIH
      entry certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults
      meaning transport conditionTree found valid unique agrees reference correct postCorrect postFailed state
    obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress⟩ :=
      condition_preserves functions program evidence meaning conditionTree found valid unique agrees state (.value conditionEvaluation)
    cases conditionRelated with
    | value payload =>
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      cases sameSource
      subst sameCore
      obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress⟩ :=
        body_preserves functions program evidence correct valid agrees reference (state.advance transport conditionProgress) (.control bodyEvaluation)
      cases bodyRelated with
      | continuing _ =>
        have bodyTotal := conditionProgress.trans bodyProgress
        obtain ⟨postStore, postMap, postWorld, postEval, postProgress⟩ := postCorrect (state.advance transport bodyTotal) true postEvaluation
        have progress := bodyTotal.trans postProgress
        have nextState := state.advance transport progress
        obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress⟩ :=
          nextIH meaning transport conditionTree found valid unique agrees reference correct postCorrect postFailed nextState
        exact ⟨result, finalStore, finalMap, finalWorld,
          ForLoop.body_continuing conditionEval bodyEval
            (by simpa only [postValues, Bool.false_eq_true, ↓reduceIte, List.append_assoc, Core.LoopExecution.entryEnvironment, List.cons_append, List.nil_append] using postEval)
            nextState.1.selfRead nativeTrace, related, progress.trans finalProgress⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedFor.Body

/-! A finite actual for-loop evaluation reconstructs condition, body and post
source traces in evaluation order. The post and body contracts are intermediate
induction results, supplied by the recursive statement tree. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedFor.Body
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedScopedStatements (Executes)
open TypedLexicalWhile (Scope ValuesContext FlowRep)
open ProtectedWhile.Body (Reflects)
open TypedImperativeFor (Progress SourceLoop post_computation)
open CompatibleExpressionPrimitives (bool_fields)
variable {entry : ProtectedExpressionMeaning.Entry} {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {contextLocation location : Location} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
  {scope : Scope}
    (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  (reflection : ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    program context evidence source certificate faults entry)
  (transport : ProtectedExpressionMeaning.Transport entry)

include reflection transport in
theorem iterations_reflect {condition : ExpressionId} {node : ExpressionNode}
    {post : List ForItemForm} {statements : List StatementId} {expected : TypeSystem.Ty}
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (correct : Reflects functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) false statements expected type code)
    (postCorrect : PostReflects functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry)
      (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := location) (type := type)
      (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) faults post postCode)
    (bodyCannotFault : ∀ {before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False) :
    ∀ (size : Nat) {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store finalStore : Store} {value : Value},
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store →
      EvaluationSize size (Core.LoopExecution.entryEnvironment type location actual) store
        (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore →
      ∃ outcome after finalMap finalWorld,
        SourceLoop program context evidence source environment before condition post statements outcome after ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  intro size
  induction size using Nat.strongRecOn with
  | ind size ih =>
    intro mapping world before store finalStore value state evaluation
    obtain ⟨conditionSize, conditionStore, conditionValue, _, conditionEval⟩ := evaluation.bind_computation
    obtain ⟨conditionOutcome, conditionHeap, conditionMap, conditionWorld, conditionTrace, conditionRelated, conditionProgress⟩ :=
      condition_reflects functions program evidence reflection conditionTree found valid agrees state conditionEval.sound
    cases conditionRelated with
    | fault matched =>
      cases conditionTrace with
      | fault failed =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound (Core.LoopExecution.condition_failure conditionEval.sound)
        exact ⟨_, conditionHeap, conditionMap, conditionWorld, .fault (.condition failed), .fault matched, conditionProgress⟩
    | value payload =>
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      subst sameSource
      subst sameCore
      cases conditionTrace with
      | value conditionTrace =>
        cases boolean with
        | false =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound (Core.LoopExecution.condition_false conditionEval.sound)
          exact ⟨_, conditionHeap, conditionMap, conditionWorld, .control (.done conditionTrace), .fallthrough environment, conditionProgress⟩
        | true =>
          obtain ⟨branchSize, branchSmaller, branch⟩ := evaluation.loop_true_branch conditionEval.sound
          obtain ⟨bodySize, bodyStore, bodyValue, _, bodyEval⟩ := branch.bind_computation
          obtain ⟨bodyContext, bodyOutcome, bodyHeap, bodyMap, bodyWorld, bodyTrace, bodyRelated, bodyProgress⟩ :=
            body_reflects functions program evidence correct valid agrees reference (state.advance transport conditionProgress) bodyEval.sound
          have progress := conditionProgress.trans bodyProgress
          cases bodyRelated with
          | fault matched =>
            cases bodyTrace with
            | control impossible => exact False.elim (bodyCannotFault impossible)
            | fault failed =>
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
                (Core.LoopExecution.body_failure conditionEval.sound bodyEval.sound)
              exact ⟨_, bodyHeap, bodyMap, bodyWorld, .fault (.body conditionTrace failed), .fault matched, progress⟩
          | returned payload =>
            cases bodyTrace with
            | control bodyTrace =>
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
                (Core.LoopExecution.body_returned conditionEval.sound bodyEval.sound)
              exact ⟨_, bodyHeap, bodyMap, bodyWorld, .control (.returns conditionTrace bodyTrace), .returned payload, progress⟩
          | breaking bodyEnvironment =>
            cases bodyTrace with
            | control bodyTrace =>
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
                (Core.LoopExecution.body_breaking conditionEval.sound bodyEval.sound)
              exact ⟨_, bodyHeap, bodyMap, bodyWorld, .control (.breaks conditionTrace bodyTrace), .fallthrough environment, progress⟩
          | fallthrough bodyEnvironment =>
            cases bodyTrace with
            | control bodyTrace =>
              obtain ⟨postStore, postValue, postEval⟩ := post_computation false branch bodyEval.sound
              rcases postCorrect (state.advance transport progress) false postEval with done | failed
              · obtain ⟨postContext, postEnvironment, postHeap, postMap, postWorld, postTrace, rfl, postProgress⟩ := done
                have prefixProgress := progress.trans postProgress
                have nextState := state.advance transport prefixProgress
                obtain ⟨nextSize, smaller, nextEval⟩ := ForLoop.next_fallthrough branch bodyEval.sound postEval nextState.1.selfRead
                obtain ⟨outcome, after, finalMap, finalWorld, nextTrace, related, nextProgress⟩ :=
                  ih nextSize (Nat.lt_trans smaller branchSmaller) nextState nextEval
                cases nextTrace with
                | control nextTrace => exact ⟨_, after, finalMap, finalWorld, .control (.nextFallthrough conditionTrace bodyTrace postTrace nextTrace), related, prefixProgress.trans nextProgress⟩
                | fault nextTrace => exact ⟨_, after, finalMap, finalWorld, .fault (.nextFallthrough conditionTrace bodyTrace postTrace nextTrace), related, prefixProgress.trans nextProgress⟩
              · obtain ⟨postContext, reason, token, postHeap, postMap, postWorld, postTrace, rfl, matched, postProgress⟩ := failed
                obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
                  (ForLoop.body_fallthrough_post_fault conditionEval.sound bodyEval.sound postEval)
                exact ⟨_, postHeap, postMap, postWorld, .fault (.postFallthrough conditionTrace bodyTrace postTrace), .fault matched, progress.trans postProgress⟩
          | continuing bodyEnvironment =>
            cases bodyTrace with
            | control bodyTrace =>
              obtain ⟨postStore, postValue, postEval⟩ := post_computation true branch bodyEval.sound
              rcases postCorrect (state.advance transport progress) true postEval with done | failed
              · obtain ⟨postContext, postEnvironment, postHeap, postMap, postWorld, postTrace, rfl, postProgress⟩ := done
                have prefixProgress := progress.trans postProgress
                have nextState := state.advance transport prefixProgress
                obtain ⟨nextSize, smaller, nextEval⟩ := ForLoop.next_continuing branch bodyEval.sound postEval nextState.1.selfRead
                obtain ⟨outcome, after, finalMap, finalWorld, nextTrace, related, nextProgress⟩ :=
                  ih nextSize (Nat.lt_trans smaller branchSmaller) nextState nextEval
                cases nextTrace with
                | control nextTrace => exact ⟨_, after, finalMap, finalWorld, .control (.nextContinue conditionTrace bodyTrace postTrace nextTrace), related, prefixProgress.trans nextProgress⟩
                | fault nextTrace => exact ⟨_, after, finalMap, finalWorld, .fault (.nextContinue conditionTrace bodyTrace postTrace nextTrace), related, prefixProgress.trans nextProgress⟩
              · obtain ⟨postContext, reason, token, postHeap, postMap, postWorld, postTrace, rfl, matched, postProgress⟩ := failed
                obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
                  (ForLoop.body_continuing_post_fault conditionEval.sound bodyEval.sound postEval)
                exact ⟨_, postHeap, postMap, postWorld, .fault (.postContinue conditionTrace bodyTrace postTrace), .fault matched, progress.trans postProgress⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedFor.Body
