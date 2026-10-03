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
open TypedImperativeFor (Progress postValues SourceLoop)
open CompatibleExpressionPrimitives (bool_fields)
open ProtectedWhile.Body (Reflects)
open RecursiveNamedForContracts (Below)
theorem iterations_success_bounded_for (validity : SourceSemantics.Context → Prop)
    {program : Program} {size : Nat} {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {post : List ForItemForm} {statements : List StatementId} {outcome : Dynamic.ControlOutcome}
    (trace : SourceExecutionSize.ForLoopExecutes program size context evidence source environment before condition post statements finalContext outcome after) :
    ∀ (budget : Nat), size ≤ budget →
    ∀ {entry : ProtectedExpressionMeaning.Entry} {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {faults : FunctionCalls.FaultRep},
      Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source certificate faults entry) →
      ProtectedExpressionMeaning.Transport entry →
      certificate scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      validity context → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      Below budget (fun size => RecursiveNamedLoopContracts.PreservesAtFor functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
        (faults := faults) (validity := validity) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) size false statements expected type code) →
      Below budget (fun size => RecursiveNamedForContracts.PostPreservesAt size functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode) →
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store →
      ∃ value finalStore finalMap finalWorld,
        Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
          (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  induction size using Nat.strongRecOn generalizing context finalContext evidence source environment before after condition post statements outcome with
  | ind size ih =>
    intro budget bounded entry certificate values scope ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults
      meaning transport conditionTree found valid unique agrees reference correct postCorrect state
    cases trace with
    | done conditionEvaluation =>
      obtain ⟨value, nextStore, nextMap, nextWorld, evaluated, represented, progress⟩ :=
        condition_preserves_at_for functions program evidence validity (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) conditionTree found valid unique agrees state (.value conditionEvaluation)
      cases represented with
      | value payload =>
        obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
        cases sameSource
        subst sameCore
        exact ⟨_, nextStore, nextMap, nextWorld, Core.LoopExecution.condition_false evaluated, .fallthrough environment, progress⟩
    | nextFallthrough conditionEvaluation bodyEvaluation postEvaluation next =>
      obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress⟩ :=
        condition_preserves_at_for functions program evidence validity (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) conditionTree found valid unique agrees state (.value conditionEvaluation)
      cases conditionRelated with
      | value payload =>
        obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
        cases sameSource
        subst sameCore
        obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress⟩ :=
          body_preserves_at_for functions program evidence validity (correct _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) valid agrees reference (state.advance transport conditionProgress) (.control bodyEvaluation)
        cases bodyRelated with
        | fallthrough _ =>
          have bodyTotal := conditionProgress.trans bodyProgress
          obtain ⟨postStore, postMap, postWorld, postEval, postProgress⟩ := (postCorrect _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) (state.advance transport bodyTotal) false postEvaluation
          have progress := bodyTotal.trans postProgress
          have nextState := state.advance transport progress
          obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress⟩ :=
            ih _ (SourceExecutionSize.child_lt_stepSize (by simp)) next budget (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) bounded) meaning transport conditionTree found valid unique agrees reference correct postCorrect nextState
          exact ⟨result, finalStore, finalMap, finalWorld,
            ForLoop.body_fallthrough conditionEval bodyEval
              (by simpa only [postValues, Bool.false_eq_true, ↓reduceIte, List.append_assoc, Core.LoopExecution.entryEnvironment, List.cons_append, List.nil_append] using postEval)
              nextState.1.selfRead nativeTrace, related, progress.trans finalProgress⟩
    | nextContinue conditionEvaluation bodyEvaluation postEvaluation next =>
      obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress⟩ :=
        condition_preserves_at_for functions program evidence validity (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) conditionTree found valid unique agrees state (.value conditionEvaluation)
      cases conditionRelated with
      | value payload =>
        obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
        cases sameSource
        subst sameCore
        obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress⟩ :=
          body_preserves_at_for functions program evidence validity (correct _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) valid agrees reference (state.advance transport conditionProgress) (.control bodyEvaluation)
        cases bodyRelated with
        | continuing _ =>
          have bodyTotal := conditionProgress.trans bodyProgress
          obtain ⟨postStore, postMap, postWorld, postEval, postProgress⟩ := (postCorrect _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) (state.advance transport bodyTotal) true postEvaluation
          have progress := bodyTotal.trans postProgress
          have nextState := state.advance transport progress
          obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress⟩ :=
            ih _ (SourceExecutionSize.child_lt_stepSize (by simp)) next budget (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) bounded) meaning transport conditionTree found valid unique agrees reference correct postCorrect nextState
          exact ⟨result, finalStore, finalMap, finalWorld,
            ForLoop.body_continuing conditionEval bodyEval
              (by simpa only [postValues, Bool.false_eq_true, ↓reduceIte, List.append_assoc, Core.LoopExecution.entryEnvironment, List.cons_append, List.nil_append] using postEval)
              nextState.1.selfRead nativeTrace, related, progress.trans finalProgress⟩
    | breaks conditionEvaluation bodyEvaluation =>
      obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress⟩ :=
        condition_preserves_at_for functions program evidence validity (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) conditionTree found valid unique agrees state (.value conditionEvaluation)
      cases conditionRelated with
      | value payload =>
        obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
        cases sameSource
        subst sameCore
        obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress⟩ :=
          body_preserves_at_for functions program evidence validity (correct _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) valid agrees reference (state.advance transport conditionProgress) (.control bodyEvaluation)
        cases bodyRelated with
        | breaking _ =>
          exact ⟨_, bodyStore, bodyMap, bodyWorld, Core.LoopExecution.body_breaking conditionEval bodyEval, .fallthrough environment, conditionProgress.trans bodyProgress⟩
    | returns conditionEvaluation bodyEvaluation =>
      obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress⟩ :=
        condition_preserves_at_for functions program evidence validity (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) conditionTree found valid unique agrees state (.value conditionEvaluation)
      cases conditionRelated with
      | value payload =>
        obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
        cases sameSource
        subst sameCore
        obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress⟩ :=
          body_preserves_at_for functions program evidence validity (correct _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) valid agrees reference (state.advance transport conditionProgress) (.control bodyEvaluation)
        cases bodyRelated with
        | returned payload =>
          exact ⟨_, bodyStore, bodyMap, bodyWorld, Core.LoopExecution.body_returned conditionEval bodyEval, .returned payload, conditionProgress.trans bodyProgress⟩

theorem iterations_success_bounded
    {program : Program} {size : Nat} {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {post : List ForItemForm} {statements : List StatementId} {outcome : Dynamic.ControlOutcome}
    (trace : SourceExecutionSize.ForLoopExecutes program size context evidence source environment before condition post statements finalContext outcome after) :
    ∀ (budget : Nat), size ≤ budget →
    ∀ {entry : ProtectedExpressionMeaning.Entry} {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope} {solved : List SolvedRequirement}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {faults : FunctionCalls.FaultRep},
      Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source certificate faults entry) →
      ProtectedExpressionMeaning.Transport entry →
      certificate scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      CompatibleExpressionLiterals.ContextValid solved context evidence → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      Below budget (fun size => ProtectedWhile.Body.PreservesAt functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
        (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) size false statements expected type code) →
      Below budget (fun size => RecursiveNamedForContracts.PostPreservesAt size functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode) →
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store →
      ∃ value finalStore finalMap finalWorld,
        Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
          (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  intro budget bounded entry certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults
      meaning transport conditionTree found valid unique agrees reference correct postCorrect state
  exact iterations_success_bounded_for (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
    trace budget bounded meaning transport conditionTree found valid unique agrees reference correct postCorrect state

theorem iterations_fault_bounded_for (validity : SourceSemantics.Context → Prop)
    {program : Program} {size : Nat} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {post : List ForItemForm} {statements : List StatementId} {reason : Dynamic.SemanticFault}
    (trace : SourceExecutionSize.ForLoopFaults program size context evidence source environment before condition post statements reason after) :
    ∀ (budget : Nat), size ≤ budget →
    ∀ {entry : ProtectedExpressionMeaning.Entry} {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {faults : FunctionCalls.FaultRep},
      Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source certificate faults entry) →
      ProtectedExpressionMeaning.Transport entry →
      certificate scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      validity context → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      Below budget (fun size => RecursiveNamedLoopContracts.PreservesAtFor functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
        (faults := faults) (validity := validity) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) size false statements expected type code) →
      Below budget (fun size => RecursiveNamedForContracts.PostPreservesAt size functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode) →
      Below budget (fun size => RecursiveNamedForContracts.PostFaultsAt size functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry) (faults := faults)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode) →
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store →
      ∃ value finalStore finalMap finalWorld,
        Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
          (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type (.fault reason) value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  induction size using Nat.strongRecOn generalizing context evidence source environment before after condition post statements reason with
  | ind size ih =>
    intro budget bounded entry certificate values scope ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults
      meaning transport conditionTree found valid unique agrees reference correct postCorrect postFailed state
    cases trace with
    | condition conditionFault =>
      obtain ⟨value, nextStore, nextMap, nextWorld, evaluated, represented, progress⟩ :=
        condition_preserves_at_for functions program evidence validity (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) conditionTree found valid unique agrees state (.fault conditionFault)
      cases represented with
      | fault matched => exact ⟨_, nextStore, nextMap, nextWorld, Core.LoopExecution.condition_failure evaluated, .fault matched, progress⟩
    | conditionType conditionEvaluation notBoolean runtimeType =>
      obtain ⟨value, nextStore, nextMap, nextWorld, evaluated, represented, progress⟩ :=
        condition_preserves_at_for functions program evidence validity (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) conditionTree found valid unique agrees state (.value conditionEvaluation)
      cases represented with
      | value payload =>
        obtain ⟨boolean, rfl, _⟩ := bool_fields payload
        exact False.elim (notBoolean trivial)
    | body conditionEvaluation bodyFault =>
      obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress⟩ :=
        condition_preserves_at_for functions program evidence validity (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) conditionTree found valid unique agrees state (.value conditionEvaluation)
      cases conditionRelated with
      | value payload =>
        obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
        cases sameSource
        subst sameCore
        obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress⟩ :=
          body_preserves_at_for functions program evidence validity (correct _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) valid agrees reference (state.advance transport conditionProgress) (.fault bodyFault)
        cases bodyRelated with
        | fault matched => exact ⟨_, bodyStore, bodyMap, bodyWorld, Core.LoopExecution.body_failure conditionEval bodyEval, .fault matched, conditionProgress.trans bodyProgress⟩
    | postFallthrough conditionEvaluation bodyEvaluation postEvaluation =>
      obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress⟩ :=
        condition_preserves_at_for functions program evidence validity (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) conditionTree found valid unique agrees state (.value conditionEvaluation)
      cases conditionRelated with
      | value payload =>
        obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
        cases sameSource
        subst sameCore
        obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress⟩ :=
          body_preserves_at_for functions program evidence validity (correct _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) valid agrees reference (state.advance transport conditionProgress) (.control bodyEvaluation)
        cases bodyRelated with
        | fallthrough _ =>
          have bodyTotal := conditionProgress.trans bodyProgress
          obtain ⟨token, postStore, postMap, postWorld, postEval, matched, postProgress⟩ :=
            (postFailed _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) (state.advance transport bodyTotal) false postEvaluation
          exact ⟨_, postStore, postMap, postWorld,
            ForLoop.body_fallthrough_post_fault conditionEval bodyEval
              (by simpa only [postValues, Bool.false_eq_true, ↓reduceIte, List.append_assoc, Core.LoopExecution.entryEnvironment, List.cons_append, List.nil_append] using postEval),
            .fault matched, bodyTotal.trans postProgress⟩
    | postContinue conditionEvaluation bodyEvaluation postEvaluation =>
      obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress⟩ :=
        condition_preserves_at_for functions program evidence validity (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) conditionTree found valid unique agrees state (.value conditionEvaluation)
      cases conditionRelated with
      | value payload =>
        obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
        cases sameSource
        subst sameCore
        obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress⟩ :=
          body_preserves_at_for functions program evidence validity (correct _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) valid agrees reference (state.advance transport conditionProgress) (.control bodyEvaluation)
        cases bodyRelated with
        | continuing _ =>
          have bodyTotal := conditionProgress.trans bodyProgress
          obtain ⟨token, postStore, postMap, postWorld, postEval, matched, postProgress⟩ :=
            (postFailed _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) (state.advance transport bodyTotal) true postEvaluation
          exact ⟨_, postStore, postMap, postWorld,
            ForLoop.body_continuing_post_fault conditionEval bodyEval
              (by simpa only [postValues, Bool.false_eq_true, ↓reduceIte, List.append_assoc, Core.LoopExecution.entryEnvironment, List.cons_append, List.nil_append] using postEval),
            .fault matched, bodyTotal.trans postProgress⟩
    | nextFallthrough conditionEvaluation bodyEvaluation postEvaluation next =>
      obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress⟩ :=
        condition_preserves_at_for functions program evidence validity (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) conditionTree found valid unique agrees state (.value conditionEvaluation)
      cases conditionRelated with
      | value payload =>
        obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
        cases sameSource
        subst sameCore
        obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress⟩ :=
          body_preserves_at_for functions program evidence validity (correct _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) valid agrees reference (state.advance transport conditionProgress) (.control bodyEvaluation)
        cases bodyRelated with
        | fallthrough _ =>
          have bodyTotal := conditionProgress.trans bodyProgress
          obtain ⟨postStore, postMap, postWorld, postEval, postProgress⟩ := (postCorrect _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) (state.advance transport bodyTotal) false postEvaluation
          have progress := bodyTotal.trans postProgress
          have nextState := state.advance transport progress
          obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress⟩ :=
            ih _ (SourceExecutionSize.child_lt_stepSize (by simp)) next budget (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) bounded) meaning transport conditionTree found valid unique agrees reference correct postCorrect postFailed nextState
          exact ⟨result, finalStore, finalMap, finalWorld,
            ForLoop.body_fallthrough conditionEval bodyEval
              (by simpa only [postValues, Bool.false_eq_true, ↓reduceIte, List.append_assoc, Core.LoopExecution.entryEnvironment, List.cons_append, List.nil_append] using postEval)
              nextState.1.selfRead nativeTrace, related, progress.trans finalProgress⟩
    | nextContinue conditionEvaluation bodyEvaluation postEvaluation next =>
      obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress⟩ :=
        condition_preserves_at_for functions program evidence validity (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) conditionTree found valid unique agrees state (.value conditionEvaluation)
      cases conditionRelated with
      | value payload =>
        obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
        cases sameSource
        subst sameCore
        obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress⟩ :=
          body_preserves_at_for functions program evidence validity (correct _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) valid agrees reference (state.advance transport conditionProgress) (.control bodyEvaluation)
        cases bodyRelated with
        | continuing _ =>
          have bodyTotal := conditionProgress.trans bodyProgress
          obtain ⟨postStore, postMap, postWorld, postEval, postProgress⟩ := (postCorrect _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) (state.advance transport bodyTotal) true postEvaluation
          have progress := bodyTotal.trans postProgress
          have nextState := state.advance transport progress
          obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress⟩ :=
            ih _ (SourceExecutionSize.child_lt_stepSize (by simp)) next budget (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) bounded) meaning transport conditionTree found valid unique agrees reference correct postCorrect postFailed nextState
          exact ⟨result, finalStore, finalMap, finalWorld,
            ForLoop.body_continuing conditionEval bodyEval
              (by simpa only [postValues, Bool.false_eq_true, ↓reduceIte, List.append_assoc, Core.LoopExecution.entryEnvironment, List.cons_append, List.nil_append] using postEval)
              nextState.1.selfRead nativeTrace, related, progress.trans finalProgress⟩

theorem iterations_fault_bounded
    {program : Program} {size : Nat} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {post : List ForItemForm} {statements : List StatementId} {reason : Dynamic.SemanticFault}
    (trace : SourceExecutionSize.ForLoopFaults program size context evidence source environment before condition post statements reason after) :
    ∀ (budget : Nat), size ≤ budget →
    ∀ {entry : ProtectedExpressionMeaning.Entry} {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope} {solved : List SolvedRequirement}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {faults : FunctionCalls.FaultRep},
      Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source certificate faults entry) →
      ProtectedExpressionMeaning.Transport entry →
      certificate scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      CompatibleExpressionLiterals.ContextValid solved context evidence → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      Below budget (fun size => ProtectedWhile.Body.PreservesAt functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
        (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) size false statements expected type code) →
      Below budget (fun size => RecursiveNamedForContracts.PostPreservesAt size functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode) →
      Below budget (fun size => RecursiveNamedForContracts.PostFaultsAt size functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry) (faults := faults)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode) →
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store →
      ∃ value finalStore finalMap finalWorld,
        Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
          (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type (.fault reason) value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  intro budget bounded entry certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults
      meaning transport conditionTree found valid unique agrees reference correct postCorrect postFailed state
  exact iterations_fault_bounded_for (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
    trace budget bounded meaning transport conditionTree found valid unique agrees reference correct postCorrect postFailed state

section BoundedReflection
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
  {budget : Nat}
  (reflection : Below budget (fun size => RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    program context evidence source certificate faults entry))
  (transport : ProtectedExpressionMeaning.Transport entry)

include reflection transport in
theorem iterations_reflect_bounded_for (validity : SourceSemantics.Context → Prop) {condition : ExpressionId} {node : ExpressionNode}
    {post : List ForItemForm} {statements : List StatementId} {expected : TypeSystem.Ty}
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (valid : validity context)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (correct : Below budget (fun size => RecursiveNamedLoopContracts.ReflectsAtFor functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
      (faults := faults) (validity := validity) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code))
    (postCorrect : Below budget (fun size => RecursiveNamedForContracts.PostReflectsAt size functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry)
      (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := location) (type := type)
      (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) faults post postCode))
    (bodyCannotFault : ∀ {before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False) :
    ∀ (size : Nat), size ≤ budget → ∀ {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store finalStore : Store} {value : Value},
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store →
      EvaluationSize size (Core.LoopExecution.entryEnvironment type location actual) store
        (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore →
      ∃ sourceSize outcome after finalMap finalWorld,
        RecursiveNamedForContracts.ForOutcome program sourceSize context evidence source environment before condition post statements outcome after ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  intro size
  induction size using Nat.strongRecOn with
  | ind size ih =>
    intro bounded mapping world before store finalStore value state evaluation
    obtain ⟨conditionSize, conditionStore, conditionValue, conditionSmaller, conditionEval⟩ := evaluation.bind_computation
    obtain ⟨conditionSourceSize, conditionOutcome, conditionHeap, conditionMap, conditionWorld, conditionTrace, conditionRelated, conditionProgress⟩ :=
      condition_reflects_at_for functions program evidence validity (reflection _ (Nat.lt_of_lt_of_le conditionSmaller bounded)) conditionTree found valid agrees state conditionEval
    cases conditionRelated with
    | fault matched =>
      cases conditionTrace with
      | fault failed =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound (Core.LoopExecution.condition_failure conditionEval.sound)
        exact ⟨_, _, conditionHeap, conditionMap, conditionWorld, .fault (.condition failed), .fault matched, conditionProgress⟩
    | value payload =>
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      subst sameSource
      subst sameCore
      cases conditionTrace with
      | value conditionTrace =>
        cases boolean with
        | false =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound (Core.LoopExecution.condition_false conditionEval.sound)
          exact ⟨_, _, conditionHeap, conditionMap, conditionWorld, .control (.done conditionTrace), .fallthrough environment, conditionProgress⟩
        | true =>
          obtain ⟨branchSize, branchSmaller, branch⟩ := evaluation.loop_true_branch conditionEval.sound
          obtain ⟨bodySize, bodyStore, bodyValue, bodySmaller, bodyEval⟩ := branch.bind_computation
          obtain ⟨bodySourceSize, bodyContext, bodyOutcome, bodyHeap, bodyMap, bodyWorld, bodyTrace, bodyRelated, bodyProgress⟩ :=
            body_reflects_at_for functions program evidence validity
              (correct _ (Nat.lt_of_lt_of_le bodySmaller (Nat.le_trans (Nat.le_of_lt branchSmaller) bounded))) valid agrees reference (state.advance transport conditionProgress) bodyEval
          have progress := conditionProgress.trans bodyProgress
          cases bodyRelated with
          | fault matched =>
            cases bodyTrace with
            | control impossible => exact False.elim (bodyCannotFault impossible.sound)
            | fault failed =>
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
                (Core.LoopExecution.body_failure conditionEval.sound bodyEval.sound)
              exact ⟨_, _, bodyHeap, bodyMap, bodyWorld, .fault (.body conditionTrace failed), .fault matched, progress⟩
          | returned payload =>
            cases bodyTrace with
            | control bodyTrace =>
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
                (Core.LoopExecution.body_returned conditionEval.sound bodyEval.sound)
              exact ⟨_, _, bodyHeap, bodyMap, bodyWorld, .control (.returns conditionTrace bodyTrace), .returned payload, progress⟩
          | breaking bodyEnvironment =>
            cases bodyTrace with
            | control bodyTrace =>
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
                (Core.LoopExecution.body_breaking conditionEval.sound bodyEval.sound)
              exact ⟨_, _, bodyHeap, bodyMap, bodyWorld, .control (.breaks conditionTrace bodyTrace), .fallthrough environment, progress⟩
          | fallthrough bodyEnvironment =>
            cases bodyTrace with
            | control bodyTrace =>
              obtain ⟨postSize, postStore, postValue, postSmaller, postEval⟩ := RecursiveNamedForContracts.post_computation_size false branch bodyEval.sound
              rcases (postCorrect _ (Nat.lt_of_lt_of_le postSmaller (Nat.le_trans (Nat.le_of_lt branchSmaller) bounded))) (state.advance transport progress) false postEval with done | failed
              · obtain ⟨postSourceSize, postContext, postEnvironment, postHeap, postMap, postWorld, postTrace, rfl, postProgress⟩ := done
                have prefixProgress := progress.trans postProgress
                have nextState := state.advance transport prefixProgress
                obtain ⟨nextSize, smaller, nextEval⟩ := ForLoop.next_fallthrough branch bodyEval.sound postEval.sound nextState.1.selfRead
                obtain ⟨nextSourceSize, outcome, after, finalMap, finalWorld, nextTrace, related, nextProgress⟩ :=
                  ih nextSize (Nat.lt_trans smaller branchSmaller)
                    (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans smaller branchSmaller)) bounded) nextState nextEval
                cases nextTrace with
                | control nextTrace => exact ⟨_, _, after, finalMap, finalWorld, .control (.nextFallthrough conditionTrace bodyTrace postTrace nextTrace), related, prefixProgress.trans nextProgress⟩
                | fault nextTrace => exact ⟨_, _, after, finalMap, finalWorld, .fault (.nextFallthrough conditionTrace bodyTrace postTrace nextTrace), related, prefixProgress.trans nextProgress⟩
              · obtain ⟨postSourceSize, postContext, reason, token, postHeap, postMap, postWorld, postTrace, rfl, matched, postProgress⟩ := failed
                obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
                  (ForLoop.body_fallthrough_post_fault conditionEval.sound bodyEval.sound postEval.sound)
                exact ⟨_, _, postHeap, postMap, postWorld, .fault (.postFallthrough conditionTrace bodyTrace postTrace), .fault matched, progress.trans postProgress⟩
          | continuing bodyEnvironment =>
            cases bodyTrace with
            | control bodyTrace =>
              obtain ⟨postSize, postStore, postValue, postSmaller, postEval⟩ := RecursiveNamedForContracts.post_computation_size true branch bodyEval.sound
              rcases (postCorrect _ (Nat.lt_of_lt_of_le postSmaller (Nat.le_trans (Nat.le_of_lt branchSmaller) bounded))) (state.advance transport progress) true postEval with done | failed
              · obtain ⟨postSourceSize, postContext, postEnvironment, postHeap, postMap, postWorld, postTrace, rfl, postProgress⟩ := done
                have prefixProgress := progress.trans postProgress
                have nextState := state.advance transport prefixProgress
                obtain ⟨nextSize, smaller, nextEval⟩ := ForLoop.next_continuing branch bodyEval.sound postEval.sound nextState.1.selfRead
                obtain ⟨nextSourceSize, outcome, after, finalMap, finalWorld, nextTrace, related, nextProgress⟩ :=
                  ih nextSize (Nat.lt_trans smaller branchSmaller)
                    (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans smaller branchSmaller)) bounded) nextState nextEval
                cases nextTrace with
                | control nextTrace => exact ⟨_, _, after, finalMap, finalWorld, .control (.nextContinue conditionTrace bodyTrace postTrace nextTrace), related, prefixProgress.trans nextProgress⟩
                | fault nextTrace => exact ⟨_, _, after, finalMap, finalWorld, .fault (.nextContinue conditionTrace bodyTrace postTrace nextTrace), related, prefixProgress.trans nextProgress⟩
              · obtain ⟨postSourceSize, postContext, reason, token, postHeap, postMap, postWorld, postTrace, rfl, matched, postProgress⟩ := failed
                obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
                  (ForLoop.body_continuing_post_fault conditionEval.sound bodyEval.sound postEval.sound)
                exact ⟨_, _, postHeap, postMap, postWorld, .fault (.postContinue conditionTrace bodyTrace postTrace), .fault matched, progress.trans postProgress⟩

include reflection transport in
theorem iterations_reflect_bounded {condition : ExpressionId} {node : ExpressionNode}
    {post : List ForItemForm} {statements : List StatementId} {expected : TypeSystem.Ty}
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (correct : Below budget (fun size => ProtectedWhile.Body.ReflectsAt functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code))
    (postCorrect : Below budget (fun size => RecursiveNamedForContracts.PostReflectsAt size functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry)
      (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := location) (type := type)
      (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) faults post postCode))
    (bodyCannotFault : ∀ {before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False) :
    ∀ (size : Nat), size ≤ budget → ∀ {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store finalStore : Store} {value : Value},
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store →
      EvaluationSize size (Core.LoopExecution.entryEnvironment type location actual) store
        (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore →
      ∃ sourceSize outcome after finalMap finalWorld,
        RecursiveNamedForContracts.ForOutcome program sourceSize context evidence source environment before condition post statements outcome after ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  apply iterations_reflect_bounded_for (functions := functions)
    (validity := fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
  all_goals assumption

end BoundedReflection
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
  intro entry certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
    contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults
    meaning transport conditionTree found valid unique agrees reference correct postCorrect state
  obtain ⟨size, sized⟩ := SourceExecutionSize.ForLoopExecutes.has_size trace
  exact iterations_success_bounded sized size (Nat.le_refl _)
    (fun child _ => RecursiveNamedBoundedContracts.preserves_at_of_unbounded meaning child)
    transport conditionTree found valid unique agrees reference
    (fun child _ => ProtectedWhile.Body.preserves_at_of_unbounded functions program evidence correct child)
    (fun child _ => postpreserves_at_of_unbounded functions program evidence post postCode postCorrect child) state

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
  intro entry certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
    contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults
    meaning transport conditionTree found valid unique agrees reference correct postCorrect postFailed state
  obtain ⟨size, sized⟩ := SourceExecutionSize.ForLoopFaults.has_size trace
  exact iterations_fault_bounded sized size (Nat.le_refl _)
    (fun child _ => RecursiveNamedBoundedContracts.preserves_at_of_unbounded meaning child)
    transport conditionTree found valid unique agrees reference
    (fun child _ => ProtectedWhile.Body.preserves_at_of_unbounded functions program evidence correct child)
    (fun child _ => postpreserves_at_of_unbounded functions program evidence post postCode postCorrect child)
    (fun child _ => postfaults_at_of_unbounded functions program evidence post postCode postFailed child) state

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
  intro size mapping world before store finalStore value state evaluation
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, rest⟩ :=
    iterations_reflect_bounded functions program evidence
      (fun child _ => RecursiveNamedBoundedContracts.reflects_at_of_unbounded reflection child)
      transport conditionTree found valid agrees reference
      (fun child _ => ProtectedWhile.Body.reflects_at_of_unbounded functions program evidence correct child)
      (fun child _ => postreflects_at_of_unbounded functions program evidence faults post postCode postCorrect child)
      bodyCannotFault size (Nat.le_refl _) state evaluation
  exact ⟨outcome, after, finalMap, finalWorld, trace.sound, rest⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedFor.Body
