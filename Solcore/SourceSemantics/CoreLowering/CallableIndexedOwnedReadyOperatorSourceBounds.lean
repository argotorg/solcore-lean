import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOperatorSourceAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedSequenceProducer

/-! Prepared unary and binary method operators with an empty output coercion
suffix retain their original compiler selection and Source operand/body grades.
Actual admitted operand posts feed the selected method invocation; broader
coercion suffixes and stored callees are outside this finite branch. -/
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReadyOperatorSourceBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open DataExpressionSequence CallablePreparedOperatorSourceBounds
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u,0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  {model : GenericHeap.PayloadModel catalog projects definitions}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {certificate : GenericExpressionMeaning.Certificate}
  {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {sourceTypes originalTypes : List TypeSystem.Ty}
  {codes : List SourceCoreBasic.LoweredExpr}

/-- The source receipt keeps each original operand's strict grade. -/
def OperandOutcomeAt (budget : Nat) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (outcome : Outcome) (after : Dynamic.Heap) : Prop :=
  match outcome with
  | .ok values => ArgumentsAt (Program.ofChecked compiled.sourceProgram) budget context evidence source environment before ids values after
  | .error reason => ArgumentsFaultAt (Program.ofChecked compiled.sourceProgram) budget context evidence source environment before ids reason after

/-- Unary/binary packaging uses the existing single child and two-child adapter.
Every successful first post supplies admission for the actual next child. -/
theorem preserves_operands (budget : Nat)
    (shape : (∃ id, ids = [id]) ∨ (∃ left right, ids = [left,right]))
    (tree : Tree source certificate scope ids sourceTypes codes)
    (unique : NodeOccurrencesUnique source) (typing : ExpressionsHaveTypes source context ids originalTypes)
    (meaning : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      model context evidence source certificate faults size)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Outcome}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : callerProtocol.State ⟨scope,mapping,world,before,store,canonical⟩)
    (admitted : Admission bridge context initial)
    (trace : OperandOutcomeAt (compiled := compiled) (context := context) (evidence := evidence) (source := source) (ids := ids) budget environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope,finalMap,finalWorld,after,finalStore,canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedExpressionSequence.PostSequenceAdmission bridge (context := context) outcome reached := by
  rcases shape with ⟨id,rfl⟩ | ⟨left,right,rfl⟩
  · cases tree with
    | single found certified =>
      have sourceTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique typing (by simp) found
      cases outcome with
      | ok values =>
        dsimp only [OperandOutcomeAt] at trace
        cases trace with
        | cons head strict tail =>
          cases tail
          obtain ⟨value,finalStore,finalMap,finalWorld,evaluated,represented,finalHeaps,maps,worlds,frame,metadata,reached,related,post⟩ :=
            meaning _ strict certified found sourceTyped environments heaps locals agrees typed initial admitted (.value head)
          cases represented with
          | @value sourceValue nativeValue payload =>
            exact ⟨_,finalStore,finalMap,finalWorld,evaluated,.values (values := [nativeValue]) (.cons payload .nil),finalHeaps,maps,worlds,frame,metadata,
              reached,related,⟨post.rows,fun _ _ => post.at_value.2⟩⟩
      | error reason =>
        dsimp only [OperandOutcomeAt] at trace
        cases trace with
        | head failed strict =>
          obtain ⟨value,finalStore,finalMap,finalWorld,evaluated,represented,finalHeaps,maps,worlds,frame,metadata,reached,related,post⟩ :=
            meaning _ strict certified found sourceTyped environments heaps locals agrees typed initial admitted (.fault failed)
          cases represented with
          | fault matched =>
            exact ⟨_,finalStore,finalMap,finalWorld,evaluated,.fault matched,finalHeaps,maps,worlds,frame,metadata,
              reached,related,⟨post.rows,by intro _ impossible; cases impossible⟩⟩
        | tail _ _ tail => cases tail
  · cases tree with
    | cons firstFound firstCertified tail =>
      cases tail with
      | single secondFound secondCertified =>
        have firstTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique typing (by simp) firstFound
        have secondTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique typing (by simp) secondFound
        cases outcome with
        | ok values =>
          dsimp only [OperandOutcomeAt] at trace
          cases trace with
          | cons head strict tail =>
            cases tail with
            | cons second secondStrict nil =>
              cases nil
              obtain ⟨value,finalStore,finalMap,finalWorld,evaluated,represented,finalHeaps,maps,worlds,frame,metadata,reached,related,post⟩ :=
                CallableIndexedOwnedAdmittedExpressionBounds.preserves_pair_after_value (bridge := bridge)
                  (meaning _ strict) (meaning _ secondStrict) firstCertified secondCertified firstFound secondFound firstTyped secondTyped
                  environments heaps locals agrees typed initial admitted (.value head) (.value second)
              exact ⟨_,finalStore,finalMap,finalWorld,evaluated,represented,finalHeaps,maps,worlds,frame,metadata,
                reached,related,⟨post.rows,fun _ _ => post.at_value.2⟩⟩
        | error reason =>
          dsimp only [OperandOutcomeAt] at trace
          cases trace with
          | head failed strict =>
            obtain ⟨value,finalStore,finalMap,finalWorld,evaluated,represented,finalHeaps,maps,worlds,frame,metadata,reached,related,post⟩ :=
              meaning _ strict firstCertified firstFound firstTyped environments heaps locals agrees typed initial admitted (.fault failed)
            cases represented with
            | fault matched =>
              refine ⟨_,finalStore,finalMap,finalWorld,?_,.fault matched,finalHeaps,maps,worlds,frame,metadata,
                reached,related,⟨post.rows,by intro _ impossible; cases impossible⟩⟩
              simpa [SourceCoreCalls.packArguments, DataExpressionSequence.pair_rename] using
                LocalSequence.pair_left_failure _ _ evaluated
          | tail first strict failed =>
            cases failed with
            | head failed secondStrict =>
              obtain ⟨value,finalStore,finalMap,finalWorld,evaluated,represented,finalHeaps,maps,worlds,frame,metadata,reached,related,post⟩ :=
                CallableIndexedOwnedAdmittedExpressionBounds.preserves_pair_after_value (bridge := bridge)
                  (meaning _ strict) (meaning _ secondStrict) firstCertified secondCertified firstFound secondFound firstTyped secondTyped
                  environments heaps locals agrees typed initial admitted (.value first) (.fault failed)
              exact ⟨_,finalStore,finalMap,finalWorld,evaluated,represented,finalHeaps,maps,worlds,frame,metadata,
                reached,related,⟨post.rows,by intro _ impossible; cases impossible⟩⟩
            | tail _ _ failed => cases failed


section MethodCall
open CallablePreparedMethodRuntimeMeaning CallableIndexedParameterMeaning
open CallableIndexedOwnedExtendedJointReadyContinuations
variable {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  {methodAdministrative : Core.Context}
  {bodySyntax : ExpressionId → Prop} {bodyCertificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {validity : SourceSemantics.Context → Prop} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (profile : CallablePreparedMethodCatalogHookMeaning.ProfileFor principal.cached.compilation (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) principal.sourceBody principal.dictionary methodAdministrative registry faults
    bodySyntax bodyCertificates validity diagnosticPolicy)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (escaped : faults .controlEscapedFunction principal.cached.compilation.own.table.escapedReason)
  (extend : ∀ {context next binder}, validity context → BinderExtends principal.sourceBody.source.owner context binder next → validity next)
  (runtimeOf : ∀ {context}, validity context →
    CompatibleRuntimeContextValidity.Valid principal.named.specialized.function.solvedRequirements context principal.dictionary)
  {headerCertificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {headerSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  (syntaxTree : GenericImperativeMatch.Syntax principal.sourceFunction.source bodySyntax profile.context
    (.statements true principal.sourceFunction.body) principal.sourceFunction.resultType)

/-- This static row conversion retains the original binder schemes and native
binder types together. It performs no evaluation recursion. -/
private theorem arguments_of_values {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {mapping : LocationMap} {world : StoreTyping} (bindings : List CallableIndexedParameterCertificates.Binding)
    {sources : List Dynamic.Value} {payloads : List Value}
    (represented : Values model mapping world (bindings.map (fun binding => binding.1.scheme.body))
      (bindings.map Prod.snd) sources payloads) : Arguments model mapping world bindings sources payloads := by
  induction bindings generalizing sources payloads with
  | nil => cases represented; exact .nil
  | cons binding rest ih => cases represented with
    | cons head tail => exact .cons head (ih tail)

include runtime covers wellFormed in
/-- The real successful operand trace authenticates the raw Source heap and
values at its actual post. The original typing row is independent of Core. -/
theorem after_operands {environment : Dynamic.Environment} {before middle : Dynamic.Heap}
    {arguments : List Dynamic.Value} {parameterTypes : List TypeSystem.Ty}
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (typedHeap : Dynamic.HeapWellTyped context before)
    (typing : ExpressionsHaveTypes source context ids parameterTypes)
    (evaluated : Dynamic.ExpressionsEvaluate (Program.ofChecked compiled.sourceProgram) context evidence source environment
      before ids arguments middle) :
    Dynamic.ValuesHaveTypes context middle arguments parameterTypes ∧ Dynamic.HeapWellTyped context middle := by
  have preserves : Dynamic.ExpressionExecutionPreserves (Program.ofChecked compiled.sourceProgram) context evidence source environment := by
    intro before after id value type covers locals typedHeap typing evaluated
    exact wellFormed.wholeLanguagePreservation.expression context evidence source environment before after id value type
      runtime covers locals typedHeap typing evaluated
  have actual := Dynamic.ExpressionsEvaluate.preserves preserves covers locals typedHeap typing evaluated
  exact ⟨actual.1, actual.2.1⟩

include syntaxTree wellFormed runtime covers escaped extend runtimeOf in
/-- Original operand grades feed the actual selected parameter/body entry.
The same base body post restores the stronger caller at its original spine. -/
theorem preserves_raw_at (budget rawBudget : Nat) (bounded : rawBudget ≤ budget)
    (below : PreservingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := headerCertificates) (expressionSyntax := headerSyntax) functions wellFormed budget)
    (shape : (∃ id, ids = [id]) ∨ (∃ left right, ids = [left,right]))
    (tree : Tree source certificate scope ids (principal.named.inputs.map (fun binding => binding.1.scheme.body)) codes)
    (nativeTypes : codes.map (·.type) = principal.named.inputs.map Prod.snd)
    (packedType : principal.named.signature.parameterType = (SourceCoreCalls.packArguments codes).type)
    (unique : NodeOccurrencesUnique source)
    {operand : TypeSystem.Ty} {parameterTypes returnTypes : List TypeSystem.Ty} {predicates : List ProgramPredicate}
    {traitName methodName : String} {requirements : List RequirementId}
    (typing : ExpressionsHaveTypes source context ids parameterTypes)
    (operatorProfile : OperatorProfileInstantiates context traitName methodName operand parameterTypes returnTypes predicates)
    (proves : RequirementSequenceProves context requirements predicates)
    (selected : Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context evidence
      traitName methodName requirements principal.sourceBody principal.dictionary)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source certificate faults size)
    {mapping : LocationMap} {world : StoreTyping} {callerAdministrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome} {reason : Word}
    (installed : Installed principal.cached.compilation (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (sourceBody := principal.sourceBody)
      (administrative := methodAdministrative) functions mapping world before store actual)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameFrame : installed.frameLocation = owner.key.frameLocation)
    (observed : CallableIndexedOwnedExpressionHeads.Globals (headers := headers) owner 0 [] installed.canonical)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) mapping world
      callerAdministrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (initial : callerProtocol.State ⟨scope,mapping,world,before,store,canonical⟩)
    (admitted : Admission bridge context initial)
    (trace : RawTraceAt (Program.ofChecked compiled.sourceProgram) rawBudget context evidence principal.dictionary source environment
      before ids principal.sourceBody outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (SourceCoreCalls.call principal.named.signature installed.globalIndex
        ((SourceCoreCalls.packArguments codes).expression.rename ξ) reason) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld principal.sourceBody.resultType principal.named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition callerProtocol initial ⟨scope,finalMap,finalWorld,after,finalStore,canonical⟩ := by
  cases trace with
  | @argumentFault sourceReason after failed =>
    obtain ⟨value,finalStore,finalMap,finalWorld,evaluated,represented,finalHeaps,maps,worlds,frame,metadata,reached,related,_post⟩ :=
      preserves_operands bridge (outcome := .error sourceReason) rawBudget shape tree unique typing
        (fun size strict => children size (Nat.lt_of_lt_of_le strict bounded))
        environments heaps locals agrees typed initial admitted failed
    cases represented with
    | fault matched =>
      exact ⟨_,finalStore,finalMap,finalWorld,SourceCoreCalls.call_argument_failure
        (signature := principal.named.signature) (index := installed.globalIndex) (internalReason := reason)
        (packedType.symm ▸ evaluated),.fault matched,finalHeaps,maps,worlds,frame,metadata,reached,related⟩
  | @apply bodySize arguments middle outcome after argumentsEvaluated called bodyStrict =>
    obtain ⟨value,middleStore,middleMap,middleWorld,argumentsEvaluation,argumentRep,middleHeaps,
        argumentMaps,argumentWorlds,argumentFrame,argumentMetadata,argumentState,argumentRelated,argumentPost⟩ :=
      preserves_operands bridge (outcome := .ok arguments) rawBudget shape tree unique typing
        (fun size strict => children size (Nat.lt_of_lt_of_le strict bounded))
        environments heaps locals agrees typed initial admitted argumentsEvaluated
    cases argumentRep with
    | @values arguments payloads represented =>
      rw [nativeTypes] at represented
      have nativeArguments := arguments_of_values principal.named.inputs represented
      let next := installed.extend argumentMaps argumentWorlds argumentFrame argumentMetadata
      have raw := after_operands wellFormed runtime covers locals admitted.heap typing argumentsEvaluated.sound
      have callee := CallableIndexedOwnedOperatorSourceAdmission.at_selected_arguments principal profile wellFormed runtime
        operatorProfile proves selected raw.2 raw.1
      obtain ⟨result,finalStore,finalMap,finalWorld,bodyEvaluation,resultRep,finalHeaps,
          bodyMaps,bodyWorlds,bodyFrame,bodyMetadata,bodyState,bodyRelated⟩ :=
        CallableIndexedOwnedExtendedReadyMethodInvocationBounds.invocation_preserves_at
          principal profile functions escaped extend runtimeOf next owner (bridge.pool argumentState)
          wellFormed callee.1 callee.2.1 (argumentPost.successful arguments rfl).rows observed syntaxTree
          nativeArguments sameFrame middleHeaps budget below called
          (Nat.le_of_lt (Nat.lt_of_lt_of_le bodyStrict bounded))
      obtain ⟨returned,_same,related⟩ := bridge.restore initial bodyState (argumentMaps.trans bodyMaps)
        (argumentWorlds.trans bodyWorlds) (argumentFrame.trans bodyFrame) (argumentMetadata.trans bodyMetadata)
        ((bridge.related argumentRelated).trans bodyRelated)
      have read := OptionalCell.read_success reason
        (show Evaluates (DataPatternValues.packValues payloads :: actual) middleStore
          (.var (installed.globalIndex + 1)) (.cellRef (OptionalCell.cellType principal.named.signature.functionType) installed.globalLocation)
          middleStore from .var installed.globalReference) next.globalRead
      exact ⟨result,finalStore,finalMap,finalWorld,SourceCoreCalls.call_success argumentsEvaluation read bodyEvaluation,
        resultRep,finalHeaps,argumentMaps.trans bodyMaps,argumentWorlds.trans bodyWorlds,
        argumentFrame.trans bodyFrame,argumentMetadata.trans bodyMetadata,returned,related⟩

/-- Actual failed operand completion fixes both the parent fault and post store.
This is the finite original call prefix inversion. -/
private theorem call_fault {signature : SourceCoreCalls.Signature} {index : Nat} {arguments : Expr} {reason : Word}
    {environment : Environment} {before middle after : Store} {token : Word} {value : Value} {size : Nat}
    (argument : Evaluates environment before arguments (.inLeft signature.parameterType (.word token)) middle)
    (completed : EvaluationSize size environment before (SourceCoreCalls.call signature index arguments reason) value after) :
    value = .inLeft signature.resultType (.word token) ∧ after = middle := by
  cases completed with
  | caseLeft actual branch =>
    obtain ⟨same,rfl⟩ := evaluation_deterministic actual.sound argument
    cases same
    cases branch with
    | inLeft payload =>
      cases payload with
      | var found =>
        simp only [List.getElem?_cons_zero,Option.some.injEq] at found
        cases found
        exact ⟨rfl,rfl⟩
  | caseRight actual _ => cases (evaluation_deterministic actual.sound argument).1

include syntaxTree wellFormed runtime covers escaped extend runtimeOf in
/-- Native operand/body prefixes retain their original strict sizes. The Source
trace is reconstructed independently at the same reached argument and body pools. -/
theorem reflects_raw_at (budget : Nat)
    (below : ReflectingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := headerCertificates) (expressionSyntax := headerSyntax) functions wellFormed budget)
    (tree : Tree source certificate scope ids (principal.named.inputs.map (fun binding => binding.1.scheme.body)) codes)
    (nativeTypes : codes.map (·.type) = principal.named.inputs.map Prod.snd)
    (packedType : principal.named.signature.parameterType = (SourceCoreCalls.packArguments codes).type)
    (unique : NodeOccurrencesUnique source)
    {operand : TypeSystem.Ty} {parameterTypes returnTypes : List TypeSystem.Ty} {predicates : List ProgramPredicate}
    {traitName methodName : String} {requirements : List RequirementId}
    (typing : ExpressionsHaveTypes source context ids parameterTypes)
    (operatorProfile : OperatorProfileInstantiates context traitName methodName operand parameterTypes returnTypes predicates)
    (proves : RequirementSequenceProves context requirements predicates)
    (selected : Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context evidence
      traitName methodName requirements principal.sourceBody principal.dictionary)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source certificate faults size)
    {mapping : LocationMap} {world : StoreTyping} {callerAdministrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value} {size : Nat} {reason : Word}
    (installed : Installed principal.cached.compilation (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (sourceBody := principal.sourceBody)
      (administrative := methodAdministrative) functions mapping world before store actual)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameFrame : installed.frameLocation = owner.key.frameLocation)
    (observed : CallableIndexedOwnedExpressionHeads.Globals (headers := headers) owner 0 [] installed.canonical)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) mapping world
      callerAdministrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (initial : callerProtocol.State ⟨scope,mapping,world,before,store,canonical⟩)
    (admitted : Admission bridge context initial)
    (completed : EvaluationSize size actual store (SourceCoreCalls.call principal.named.signature installed.globalIndex
      ((SourceCoreCalls.packArguments codes).expression.rename ξ) reason) value finalStore)
    (within : size ≤ budget) :
    ∃ outcome after finalMap finalWorld,
      NamedCalls.Arguments.Trace (Program.ofChecked compiled.sourceProgram) context evidence principal.dictionary source environment
        before ids principal.sourceBody outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld principal.sourceBody.resultType principal.named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition callerProtocol initial ⟨scope,finalMap,finalWorld,after,finalStore,canonical⟩ := by
  obtain ⟨argumentSize,argumentValue,middleStore,argumentStrict,argumentEvaluation⟩ :=
    RecursiveNamedCallBounds.call_arguments completed
  obtain ⟨_sourceSize,argumentOutcome,middle,middleMap,middleWorld,argumentTrace,argumentRep,middleHeaps,
      argumentMaps,argumentWorlds,argumentFrame,argumentMetadata,argumentState,argumentRelated,argumentPost⟩ :=
    CallableIndexedOwnedAdmittedExpressionSequence.reflects_bounded bridge budget tree unique typing children
      environments heaps locals agrees typed initial admitted argumentEvaluation (Nat.lt_of_lt_of_le argumentStrict within)
  cases argumentRep with
  | fault matched =>
    cases argumentTrace with
    | fault failed =>
      obtain ⟨rfl,rfl⟩ := call_fault (packedType.symm ▸ argumentEvaluation.sound) completed
      exact ⟨.fault _,middle,middleMap,middleWorld,.argumentFault failed.sound,.fault matched,middleHeaps,
        argumentMaps,argumentWorlds,argumentFrame,argumentMetadata,argumentState,argumentRelated⟩
  | @values arguments payloads represented =>
    cases argumentTrace with
    | values evaluatedArguments =>
      rw [nativeTypes] at represented
      have nativeArguments := arguments_of_values principal.named.inputs represented
      let next := installed.extend argumentMaps argumentWorlds argumentFrame argumentMetadata
      have raw := after_operands wellFormed runtime covers locals admitted.heap typing evaluatedArguments.sound
      have callee := CallableIndexedOwnedOperatorSourceAdmission.at_selected_arguments principal profile wellFormed runtime
        operatorProfile proves selected raw.2 raw.1
      obtain ⟨bodySize,bodyStrict,bodyEvaluation⟩ := RecursiveNamedCallBounds.call_body
        argumentEvaluation.sound installed.globalReference next.globalRead completed
      obtain ⟨sourceSize,outcome,after,finalMap,finalWorld,bodyTrace,resultRep,finalHeaps,
          bodyMaps,bodyWorlds,bodyFrame,bodyMetadata,bodyState,bodyRelated⟩ :=
        CallableIndexedOwnedExtendedReadyMethodInvocationBounds.invocation_reflects_at
          principal profile functions escaped extend runtimeOf next owner (bridge.pool argumentState)
          wellFormed callee.1 callee.2.1 (argumentPost.successful arguments rfl).rows observed syntaxTree
          nativeArguments sameFrame middleHeaps budget below bodyEvaluation
          (Nat.le_of_lt (Nat.lt_of_lt_of_le bodyStrict within))
      obtain ⟨returned,_same,related⟩ := bridge.restore initial bodyState (argumentMaps.trans bodyMaps)
        (argumentWorlds.trans bodyWorlds) (argumentFrame.trans bodyFrame) (argumentMetadata.trans bodyMetadata)
        ((bridge.related argumentRelated).trans bodyRelated)
      refine ⟨outcome,after,finalMap,finalWorld,?_,resultRep,finalHeaps,argumentMaps.trans bodyMaps,
        argumentWorlds.trans bodyWorlds,argumentFrame.trans bodyFrame,argumentMetadata.trans bodyMetadata,returned,related⟩
      cases bodyTrace with
      | value invoked => exact .apply evaluatedArguments.sound (.value invoked.sound)
      | fault failed => exact .apply evaluatedArguments.sound (.fault failed.sound)

section Parent
open CallablePreparedMethodSelection CallableCoercionExpressionCertificates
variable {project : Projector} {callerFunction : Specialized} {compilation : SourceCoreFunctions.Context}
  {child : SourceCoreEvidence.Child} {fuel : Nat} {id : ExpressionId} {reasonAt : ExpressionId → Word}
  {policy : SourceCoreFunctions.CallablePolicy} {node : ExpressionNode} {output : Lowered}
  (receipt : Operator compiled.sourceProgram project callerFunction compilation child fuel source scope id reasonAt policy node output)
  (alignment : OperatorAlignment (named := principal.named) (sourceBody := principal.sourceBody) (dictionary := principal.dictionary) receipt)
  (operatorSource : OperatorSource receipt)
  (anchor : Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context evidence
    operatorSource.traitName operatorSource.methodName receipt.requirements principal.sourceBody principal.dictionary)
  (catalogIdentity : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (ledger : context.solvedRequirements = callerFunction.function.solvedRequirements)

include alignment in
private theorem output_type (coercions : node.coercions = []) :
    output.type = principal.named.signature.resultType := by
  have suffix := receipt.suffix.accepted
  rw [coercions] at suffix
  have same : receipt.operand = output := Except.ok.inj suffix
  rw [← same,receipt.native.emitted,alignment.signature]

include syntaxTree wellFormed runtime covers escaped extend runtimeOf alignment operatorSource anchor catalogIdentity ledger in
/-- The complete original prepared parent keeps its actual Source dictionary.
Empty coercions expose the raw call, whose real reached pool supplies admission. -/
theorem preserves_at (budget size : Nat) (within : size ≤ budget)
    (below : PreservingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := headerCertificates) (expressionSyntax := headerSyntax) functions wellFormed budget)
    (coercions : node.coercions = [])
    (tree : Tree source certificate scope receipt.arguments (principal.named.inputs.map (fun binding => binding.1.scheme.body)) receipt.loweredArguments)
    (nativeTypes : receipt.loweredArguments.map (·.type) = principal.named.inputs.map Prod.snd)
    (unique : NodeOccurrencesUnique source) (parentTyped : ExpressionHasType source context id node.type)
    (children : ∀ childSize, childSize < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source certificate faults childSize)
    {mapping : LocationMap} {world : StoreTyping} {callerAdministrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    (installed : Installed principal.cached.compilation (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (sourceBody := principal.sourceBody)
      (administrative := methodAdministrative) functions mapping world before store actual)
    (located : installed.globalIndex = ξ (scope.length + compilation.administrativePrefix + receipt.native.index))
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameFrame : installed.frameLocation = owner.key.frameLocation)
    (observed : CallableIndexedOwnedExpressionHeads.Globals (headers := headers) owner 0 [] installed.canonical)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) mapping world
      callerAdministrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (initial : callerProtocol.State ⟨scope,mapping,world,before,store,canonical⟩)
    (admitted : Admission bridge context initial)
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size context evidence source environment
      before id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (output.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope,finalMap,finalWorld,after,finalStore,canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge context node.type outcome reached := by
  obtain ⟨operand,parameterTypes,returnTypes,predicates,sourceTyping,operatorProfile,proves,resultType⟩ :=
    CallableIndexedOwnedOperatorSourceAdmission.source_facts operatorSource unique coercions parentTyped
  obtain ⟨_,_,_,bodyResult⟩ := anchor.certificateOfProfile wellFormed runtime.signatures runtime.requirements.idsUnique operatorProfile proves
  have sameResult : principal.sourceBody.resultType = node.type := bodyResult.trans resultType.symm
  have packedType : principal.named.signature.parameterType = (SourceCoreCalls.packArguments receipt.loweredArguments).type := by
    simpa only [alignment.signature] using receipt.native.inputType
  have emitted := alignment.emitted receipt coercions ξ
  rw [← located] at emitted
  have shape : (∃ id, receipt.arguments = [id]) ∨ (∃ left right, receipt.arguments = [left,right]) := by
    rcases receipt.form with ⟨_,operand,_,arguments⟩ | ⟨_,left,right,_,arguments⟩
    · exact .inl ⟨operand,arguments⟩
    · exact .inr ⟨left,right,arguments⟩
  have run : ∀ {rawSize rawOutcome rawAfter dictionary},
      Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context evidence
        operatorSource.traitName operatorSource.methodName receipt.requirements principal.sourceBody dictionary →
      RawTraceAt (Program.ofChecked compiled.sourceProgram) rawSize context evidence dictionary source environment
        before receipt.arguments principal.sourceBody rawOutcome rawAfter → rawSize < size →
      ∃ value finalStore finalMap finalWorld,
        Evaluates actual store (output.expression.rename ξ) value finalStore ∧
        GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          finalMap finalWorld node.type output.type faults rawOutcome value ∧
        CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld rawAfter finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before rawAfter ∧
        ProtectedStateTransition.Transition callerProtocol initial ⟨scope,finalMap,finalWorld,rawAfter,finalStore,canonical⟩ := by
    intro rawSize rawOutcome rawAfter dictionary actualSelected rawTrace rawStrict
    let actualPrincipal := CallableIndexedOwnedMethodPrincipal.of_selected principal.cached actualSelected
    let actualProfile := CallableIndexedOwnedOperatorSourceAdmission.with_dictionary principal profile dictionary actualPrincipal.dictionary_covers
    have actualExtend : ∀ {context next binder},
        CallableIndexedOwnedOperatorSourceAdmission.EvidenceValidity (validity := validity) dictionary context →
        BinderExtends principal.sourceBody.source.owner context binder next →
        CallableIndexedOwnedOperatorSourceAdmission.EvidenceValidity (validity := validity) dictionary next :=
      fun valid extended => CallableIndexedOwnedOperatorSourceAdmission.evidence_extend (principal := principal) dictionary extend valid extended
    have actualRuntime : ∀ {context},
        CallableIndexedOwnedOperatorSourceAdmission.EvidenceValidity (validity := validity) dictionary context →
        CompatibleRuntimeContextValidity.Valid principal.named.specialized.function.solvedRequirements context dictionary :=
      fun valid => CallableIndexedOwnedOperatorSourceAdmission.evidence_runtime (principal := principal) dictionary runtimeOf valid
    obtain ⟨value,finalStore,finalMap,finalWorld,evaluated,resultRep,finalHeaps,maps,worlds,frame,metadata,transition⟩ :=
      preserves_raw_at bridge actualPrincipal actualProfile functions escaped actualExtend actualRuntime wellFormed runtime covers syntaxTree
        budget rawSize (Nat.le_of_lt (Nat.lt_of_lt_of_le rawStrict within)) below shape tree nativeTypes packedType unique
        sourceTyping operatorProfile proves actualSelected children installed owner sameFrame observed environments heaps locals agrees typed initial admitted rawTrace
    change FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      finalMap finalWorld principal.sourceBody.resultType principal.named.signature.resultType faults rawOutcome value at resultRep
    rw [sameResult,← output_type principal receipt alignment coercions] at resultRep
    exact ⟨value,finalStore,finalMap,finalWorld,emitted.symm ▸ evaluated,resultRep,finalHeaps,maps,worlds,frame,metadata,transition⟩
  have raw := CallablePreparedOperatorSourceBounds.OperatorSource.source_inv_sized operatorSource catalogIdentity ledger anchor unique trace
  have finished : ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (output.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition callerProtocol initial ⟨scope,finalMap,finalWorld,after,finalStore,canonical⟩ := by
    cases raw with
    | @rawFault rawSize sourceReason sourceAfter raw strict =>
      obtain ⟨dictionary,actualSelected,rawTrace⟩ := raw
      exact run (rawOutcome := .fault sourceReason) (rawAfter := after) actualSelected rawTrace strict
    | path raw path rawStrict _ =>
      obtain ⟨dictionary,actualSelected,rawTrace⟩ := raw
      cases outcome with
      | value value =>
        dsimp only [PathAt] at path
        rw [coercions] at path
        cases path
        exact run actualSelected rawTrace rawStrict
      | fault reason =>
        dsimp only [PathAt] at path
        rw [coercions] at path
        cases path
  obtain ⟨value,finalStore,finalMap,finalWorld,evaluated,resultRep,finalHeaps,maps,worlds,frame,metadata,reached,related⟩ := finished
  exact ⟨value,finalStore,finalMap,finalWorld,evaluated,resultRep,finalHeaps,maps,worlds,frame,metadata,reached,related,
    after_expression_sized (bridge := bridge) initial reached admitted wellFormed runtime covers locals parentTyped trace frame⟩

include syntaxTree wellFormed runtime covers escaped extend runtimeOf alignment operatorSource anchor in
/-- The measured native parent reflects its own strict operand/body prefixes.
A genuine Source parent is independently reconstructed, then authenticates the
successful raw heap at that identical returned caller state. -/
theorem reflects_at (budget size : Nat) (within : size ≤ budget)
    (below : ReflectingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := headerCertificates) (expressionSyntax := headerSyntax) functions wellFormed budget)
    (coercions : node.coercions = [])
    (tree : Tree source certificate scope receipt.arguments (principal.named.inputs.map (fun binding => binding.1.scheme.body)) receipt.loweredArguments)
    (nativeTypes : receipt.loweredArguments.map (·.type) = principal.named.inputs.map Prod.snd)
    (unique : NodeOccurrencesUnique source) (parentTyped : ExpressionHasType source context id node.type)
    (children : ∀ childSize, childSize < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source certificate faults childSize)
    {mapping : LocationMap} {world : StoreTyping} {callerAdministrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (installed : Installed principal.cached.compilation (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (sourceBody := principal.sourceBody)
      (administrative := methodAdministrative) functions mapping world before store actual)
    (located : installed.globalIndex = ξ (scope.length + compilation.administrativePrefix + receipt.native.index))
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameFrame : installed.frameLocation = owner.key.frameLocation)
    (observed : CallableIndexedOwnedExpressionHeads.Globals (headers := headers) owner 0 [] installed.canonical)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) mapping world
      callerAdministrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (initial : callerProtocol.State ⟨scope,mapping,world,before,store,canonical⟩)
    (admitted : Admission bridge context initial)
    (completed : EvaluationSize size actual store (output.expression.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context evidence source environment
        before id outcome after ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope,finalMap,finalWorld,after,finalStore,canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge context node.type outcome reached := by
  obtain ⟨operand,parameterTypes,returnTypes,predicates,sourceTyping,operatorProfile,proves,resultType⟩ :=
    CallableIndexedOwnedOperatorSourceAdmission.source_facts operatorSource unique coercions parentTyped
  obtain ⟨_,_,_,bodyResult⟩ := anchor.certificateOfProfile wellFormed runtime.signatures runtime.requirements.idsUnique operatorProfile proves
  have sameResult : principal.sourceBody.resultType = node.type := bodyResult.trans resultType.symm
  have packedType : principal.named.signature.parameterType = (SourceCoreCalls.packArguments receipt.loweredArguments).type := by
    simpa only [alignment.signature] using receipt.native.inputType
  have emitted := alignment.emitted receipt coercions ξ
  rw [← located] at emitted
  rw [emitted] at completed
  obtain ⟨outcome,after,finalMap,finalWorld,rawTrace,resultRep,finalHeaps,maps,worlds,frame,metadata,reached,related⟩ :=
    reflects_raw_at bridge principal profile functions escaped extend runtimeOf wellFormed runtime covers syntaxTree
      budget below tree nativeTypes packedType unique sourceTyping operatorProfile proves anchor children installed
      owner sameFrame observed environments heaps locals agrees typed initial admitted completed within
  rw [sameResult,← output_type principal receipt alignment coercions] at resultRep
  have sourceTrace := operatorSource.expression anchor coercions rawTrace
  obtain ⟨sourceSize,sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size sourceTrace
  exact ⟨sourceSize,outcome,after,finalMap,finalWorld,sized,resultRep,finalHeaps,maps,worlds,frame,metadata,reached,related,
    after_expression_sized (bridge := bridge) initial reached admitted wellFormed runtime covers locals parentTyped sized frame⟩
end Parent
end MethodCall

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReadyOperatorSourceBounds
