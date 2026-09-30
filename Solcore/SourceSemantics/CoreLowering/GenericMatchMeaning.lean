import Solcore.SourceSemantics.CoreLowering.GenericMatchScrutinee
import Solcore.SourceSemantics.CoreLowering.GenericLexicalContext

/-! A compositional match reflection interface. Child obligations are universal
semantic theorems for their static compiler certificates, not supplied source
executions. The match theorem constructs its source trace from Core evaluation.
This does not instantiate a general function compiler theorem: expression and
statement child correspondences remain explicit obligations. Pattern inputs
remain in the authenticated finite-value profile; unrelated heap payloads may
use the full supplied world-indexed model. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericMatchMeaning
open Core Frontend Frontend.SourceInference GeneralHeap CoreProof ReadOnly
open DataMatchCertificates DataMatchDecision DataMatchBranchPrefix GenericMatchAllocation
open SourceCoreDataMatches GenericLexicalContext

abbrev FaultRep := Dynamic.SemanticFault → Word → Prop

inductive ExpressionOutcomeRepresents (catalog : SourceCoreDataCatalog.Catalog)
    (signatures : ProgramSignatures) (sourceType : TypeSystem.Ty) (payload : Ty) (faults : FaultRep) :
    Dynamic.ExpressionOutcome → Value → Prop where
  | value {source value}
      (represented : DataPatternTypedValues.TypedValueRep catalog signatures sourceType source value) :
      ExpressionOutcomeRepresents catalog signatures sourceType payload faults (.value source) (.inRight .word value)
  | fault {reason token} (represented : faults reason token) :
      ExpressionOutcomeRepresents catalog signatures sourceType payload faults (.fault reason) (.inLeft payload (.word token))

inductive OutcomeRepresents {catalog : SourceCoreDataCatalog.Catalog} (model : GenericHeap.PayloadModel catalog)
    (mapping : LocationMap) (world : StoreTyping) (sourceType : TypeSystem.Ty) (type : Ty) (faults : FaultRep) :
    Dynamic.ControlOutcome → Value → Prop where
  | fallthrough (environment) : OutcomeRepresents model mapping world sourceType type faults
      (.fallthrough environment) (.inRight .word (.inLeft LocalLoop.transferType (.inLeft type .unit)))
  | returned {source value} (represented : model.Represents mapping world sourceType source value type) :
      OutcomeRepresents model mapping world sourceType type faults (.returned source)
        (.inRight .word (.inLeft LocalLoop.transferType (.inRight .unit value)))
  | breaking (environment) : OutcomeRepresents model mapping world sourceType type faults (.breaking environment)
      (.inRight .word (.inRight (LocalControl.controlType type) (.inLeft .unit .unit)))
  | continuing (environment) : OutcomeRepresents model mapping world sourceType type faults (.continuing environment)
      (.inRight .word (.inRight (LocalControl.controlType type) (.inRight .unit .unit)))
  | fault {reason token} (represented : faults reason token) :
      OutcomeRepresents model mapping world sourceType type faults (.fault reason) (.inLeft (LocalLoop.controlType type) (.word token))

theorem OutcomeRepresents.restore {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
    {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty} {type : Ty} {faults : FaultRep}
    {outcome : Dynamic.ControlOutcome} {value : Value}
    (represented : OutcomeRepresents model mapping world sourceType type faults outcome value)
    (environment : Dynamic.Environment) :
    OutcomeRepresents model mapping world sourceType type faults (Dynamic.restoreControl environment outcome) value := by
  cases represented with
  | fallthrough => exact .fallthrough _
  | returned value => exact .returned value
  | breaking => exact .breaking _
  | continuing => exact .continuing _
  | fault value => exact .fault value

/-- The expression compiler's universally quantified reflection obligation.
It includes exact source metadata type, effects, heap correspondence, map/world
extension and preservation of pre-existing administrative cells. -/
def ExpressionReflects (compilation : DataPatternCertificates.Compilation)
    (model : GenericHeap.PayloadModel compilation.checked.catalog) (program : Program)
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (certificate : ExpressionCertificate) (faults : FaultRep) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual before store ξ value finalStore},
    DataHeap.EnvRepresents compilation.checked.catalog mapping world administrativeContext scope environment canonical →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    Evaluates actual store (lowered.expression.rename ξ) value finalStore →
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after ∧
      ExpressionOutcomeRepresents compilation.checked.catalog compilation.signatures node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

/-- The selected-body compiler's universal reflection obligation. Its source
context is supplied by independent declarative statement typing. There is no
premise giving a source body evaluation. -/
def BodyReflects (compilation : DataPatternCertificates.Compilation)
    (model : GenericHeap.PayloadModel compilation.checked.catalog) (program : Program)
    (control : ControlContext) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (certificate : BodyCertificate) (resultSource : TypeSystem.Ty) (resultType : Ty) (faults : FaultRep) : Prop :=
  ∀ {scope statements code}, certificate scope statements code →
  ∀ {context staticFinal facts}, StatementsHaveType source control context statements staticFinal facts →
  ∀ {mapping world administrativeContext environment canonical actual before store ξ value finalStore},
    DataHeap.EnvRepresents compilation.checked.catalog mapping world administrativeContext scope environment canonical →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    Evaluates actual store (code.rename ξ) value finalStore →
    ∃ finalContext outcome after finalMap finalWorld,
      Dynamic.StatementsExecuteOutcome program context evidence source environment before statements finalContext outcome after ∧
      OutcomeRepresents model finalMap finalWorld resultSource resultType faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

private theorem read_contains {checked : SourceCoreDataCatalog.Checked} {source : TypedSource} {id : StatementId}
    {node : StatementNode} {type : Ty}
    (read : SourceCoreGeneralTypes.readStatement checked source id = .ok (node, type)) : ContainsStatement source id node := by
  by_cases owned : id.occurrence.owner = source.owner
  · simp only [SourceCoreGeneralTypes.readStatement, owned, ne_eq, not_true_eq_false, ↓reduceIte,
      pure, Except.pure, bind, Except.bind] at read
    cases found : source.lookupStatement? id with
    | none => simp [found] at read
    | some selected =>
      simp only [found] at read
      cases projected : SourceCoreGeneralTypes.projectType checked (.occurrence id.occurrence) selected.type with
      | error => simp [projected] at read
      | ok projectedType =>
        simp only [projected, Except.ok.injEq, Prod.mk.injEq] at read
        rcases read with ⟨rfl, rfl⟩
        exact lookupStatement?_sound found
  · simp [SourceCoreGeneralTypes.readStatement, owned, bind, Except.bind] at read

private theorem initial_evaluation {actual : Environment} {before after : Store}
    {code body : Expr} {type payload : Ty} {ξ : Renaming} {result : Value}
    (evaluation : Evaluates actual before ((LocalSequence.letInitialized type payload code body).rename ξ) result after) :
    ∃ value middle, Evaluates actual before (code.rename ξ) value middle := by
  rw [LoopRenaming.letInitialized] at evaluation
  cases evaluation with
  | caseLeft evaluated _ => exact ⟨_, _, evaluated⟩
  | caseRight evaluated _ => exact ⟨_, _, evaluated⟩

private theorem default_selected {context : SourceSemantics.Context} {value : Dynamic.Value}
    {cases : List TypedMatchCase} {fallback : Option (List StatementId)} {statements : List StatementId}
    (selected : Dynamic.MatchCasesSelect context value cases fallback (.default statements)) :
    fallback = some statements := by
  cases selected with
  | default => rfl
  | tail _ next => exact default_selected next
termination_by cases.length
decreasing_by simp_all

/-- Core-only reflection for one accepted match certificate. Expression and
body compiler correctness are explicit universal induction hypotheses. The
source scrutinee trace, arm choice and binder allocations are all constructed.
The result carries effects and restores the match's entry lexical scope. -/
theorem Certificate.reflects
    {compilation : DataPatternCertificates.Compilation} {model : GenericHeap.PayloadModel compilation.checked.catalog}
    (includes : IncludesFinite compilation.signatures model)
    {program : Program} {context : SourceSemantics.Context} {control : ControlContext}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultSource : TypeSystem.Ty} {resultType : Ty}
    {internalReason : Word} {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate}
    {faults : FaultRep} {code : Expr}
    (certificate : DataMatchCertificates.Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code)
    (expressionMeaning : ExpressionReflects compilation model program context evidence source expressionCertificate faults)
    (bodyMeaning : BodyReflects compilation model program control evidence source bodyCertificate resultSource resultType faults)
    (valid : DataPatternLeaves.ContextValid compilation context)
    {scrutineeNode : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some scrutineeNode)
    {caseFacts : List BodyFacts}
    (casesTyped : MatchCasesHaveType source control context scrutineeNode.type resolution.cases caseFacts)
    (defaultTyped : ∀ {statements}, resolution.defaultBody = some statements →
      ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {result : Value}
    (environments : DataHeap.EnvRepresents compilation.checked.catalog mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (evaluated : Evaluates actual store (code.rename ξ) result finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.StatementExecutesOutcome program context evidence source environment before id context outcome after ∧
      OutcomeRepresents model finalMap finalWorld resultSource resultType faults outcome result ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  cases certificate with
  | @matchWith node statementType certifiedNode payload computation arms fallback read allowed form requirements
      hiddenOwned hiddenFresh scrutineeOwned scrutineeFound projection expression sameType armsCertified fallbackCertified =>
    have same := Option.some.inj (found.symm.trans scrutineeFound)
    subst certifiedNode
    have contains := read_contains read
    have scrutineeContains := lookupExpression?_sound found
    obtain ⟨value, middleStore, initialEval⟩ := initial_evaluation evaluated
    obtain ⟨sourceOutcome, middleHeap, middleMap, middleWorld, sourceEval, outcomeRep,
      middleRelated, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
      expressionMeaning expression found environments heaps locals layout initialEval
    cases outcomeRep with
    | @fault reason token faultRepresented =>
      cases sourceEval with
      | fault sourceFault =>
        have failed : Evaluates actual store
            ((LocalSequence.letInitialized (LocalLoop.controlType resultType) payload computation.expression
              (.caseE (.loadCell (.var 0))
                (LanguageResult.failure (LocalLoop.controlType resultType) (.word internalReason))
                (arms.foldr (fun (pattern, body) next => attempt pattern (LocalLoop.controlType resultType) body next)
                  (fallback.weakenAt 0)))).rename ξ)
            (.inLeft (LocalLoop.controlType resultType) (.word token)) middleStore := by
          rw [LoopRenaming.letInitialized]
          exact LocalSequence.letInitialized_failure _ _ (by simpa only [← sameType] using initialEval)
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated failed
        exact ⟨_, middleHeap, middleMap, middleWorld, .fault (.matchScrutinee contains form sourceFault),
          .fault faultRepresented, middleRelated, firstMaps, firstWorlds, firstFrame, firstMetadata⟩
    | @value sourceValue value represented =>
      cases sourceEval with
      | value sourceEval =>
        obtain ⟨hiddenHeap, location, selection, finalScope, selectedEnvironment, selectedHeap, selectedCanonical,
          selectedActual, selectedStore, selectedMap, selectedWorld, selectedEmbedding, body,
          hiddenAllocated, selected, selectedBody, selectedEnv, selectedRelated, secondMaps, secondWorlds,
          secondFrame, selectedLayout, agreement⟩ :=
          GenericMatchScrutinee.success_prefix includes hiddenFresh (DataPatternBindings.projected_raw projection)
            armsCertified fallbackCertified valid represented (environments.extend firstMaps firstWorlds)
            middleRelated layout initialEval
        have bodyEval := agreement.unwrap evaluated
        cases selectedBody with
        | @arm statements bindings compiledBindings finalEnvironment finalHeap body binders allocated bodyCertified =>
          obtain ⟨armContext, staticFinal, facts, extended, typed, _⟩ :=
            DataMatchSourceScopes.MatchCasesSelect.arm_scope casesTyped selected
          obtain ⟨finalContext, outcome, after, finalMap, finalWorld, sourceBody, related,
            finalHeapRep, thirdMaps, thirdWorlds, thirdFrame, thirdMetadata⟩ :=
            bodyMeaning bodyCertified typed selectedEnv selectedRelated (binders_agree extended
                (arm_monomorphic casesTyped selected)
                (locals.mono (firstMetadata.trans (.of_allocation hiddenAllocated))) allocated) selectedLayout bodyEval
          have sourceMatch : Dynamic.StatementExecutesOutcome program context evidence source environment before id context
              (Dynamic.restoreControl environment outcome) after := by
            cases sourceBody with
            | control executes =>
              exact .control (.matchArm contains form scrutineeContains sourceEval hiddenAllocated selected
                rfl rfl extended allocated executes)
            | fault fault =>
              exact .fault (.matchArmBody contains form scrutineeContains sourceEval hiddenAllocated selected
                rfl rfl extended allocated fault)
          exact ⟨_, after, finalMap, finalWorld, sourceMatch, related.restore environment, finalHeapRep,
            firstMaps.trans (secondMaps.trans thirdMaps), firstWorlds.trans (secondWorlds.trans thirdWorlds),
            firstFrame.trans (secondFrame.trans thirdFrame),
            firstMetadata.trans ((Dynamic.HeapMetadataExtend.of_allocation hiddenAllocated).trans
              ((binders_metadata allocated).trans thirdMetadata))⟩
        | @default statements body bodyCertified =>
          have defaultSelected := default_selected selected
          obtain ⟨staticFinal, facts, typed⟩ := defaultTyped defaultSelected
          obtain ⟨finalContext, outcome, after, finalMap, finalWorld, sourceBody, related,
            finalHeapRep, thirdMaps, thirdWorlds, thirdFrame, thirdMetadata⟩ :=
            bodyMeaning bodyCertified typed selectedEnv selectedRelated
              (locals.mono (firstMetadata.trans (.of_allocation hiddenAllocated))) selectedLayout bodyEval
          have sourceMatch : Dynamic.StatementExecutesOutcome program context evidence source environment before id context
              (Dynamic.restoreControl environment outcome) after := by
            cases sourceBody with
            | control executes => exact .control (.matchDefault contains form scrutineeContains sourceEval hiddenAllocated selected executes)
            | fault fault => exact .fault (.matchDefaultBody contains form scrutineeContains sourceEval hiddenAllocated selected fault)
          exact ⟨_, after, finalMap, finalWorld, sourceMatch, related.restore environment, finalHeapRep,
            firstMaps.trans (secondMaps.trans thirdMaps), firstWorlds.trans (secondWorlds.trans thirdWorlds),
            firstFrame.trans (secondFrame.trans thirdFrame),
            firstMetadata.trans ((Dynamic.HeapMetadataExtend.of_allocation hiddenAllocated).trans thirdMetadata)⟩
        | noBranch =>
          have finished : Evaluates selectedActual selectedStore
              ((LocalLoop.fallthrough resultType).rename selectedEmbedding)
              (.inRight .word (.inLeft LocalLoop.transferType (.inLeft resultType .unit))) selectedStore :=
            .inRight (.inLeft (.inLeft .unit))
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic bodyEval finished
          exact ⟨.fallthrough environment, hiddenHeap, selectedMap, selectedWorld,
            .control (.matchNoBranch contains form scrutineeContains sourceEval hiddenAllocated selected),
            .fallthrough environment, selectedRelated, firstMaps.trans secondMaps, firstWorlds.trans secondWorlds,
            firstFrame.trans secondFrame, firstMetadata.trans (.of_allocation hiddenAllocated)⟩

/-- Actual successful lowering feeds the static certificate extractor and the
match reflection theorem. Callback extraction and child semantics are exposed
separately, so no semantic premise is hidden inside compiler acceptance. -/
theorem lowerWithReasons_reflects
    {compilation : DataPatternCertificates.Compilation} {model : GenericHeap.PayloadModel compilation.checked.catalog}
    (includes : IncludesFinite compilation.signatures model)
    {program : Program} {context : SourceSemantics.Context} {control : ControlContext}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultSource : TypeSystem.Ty} {resultType : Ty}
    {internalReason : Word} {reasonAt : ExpressionId → Word}
    {lowerExpression : ExpressionLowerer} {lowerBody : BodyLowerer} {fuel : Nat}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {faults : FaultRep} {code : Expr}
    (expressionExtract : ∀ childFuel scope id result,
      lowerExpression childFuel source scope id reasonAt = .ok result → expressionCertificate scope id result)
    (bodyExtract : ∀ childFuel scope statements code,
      lowerBody childFuel source scope statements resultType reasonAt internalReason = .ok code →
      bodyCertificate scope statements code)
    (accepted : lowerWithReasons compilation lowerExpression lowerBody fuel source scope id resolution
      resultType reasonAt internalReason = .ok code)
    (expressionMeaning : ExpressionReflects compilation model program context evidence source expressionCertificate faults)
    (bodyMeaning : BodyReflects compilation model program control evidence source bodyCertificate resultSource resultType faults)
    (valid : DataPatternLeaves.ContextValid compilation context)
    {scrutineeNode : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some scrutineeNode)
    {caseFacts : List BodyFacts}
    (casesTyped : MatchCasesHaveType source control context scrutineeNode.type resolution.cases caseFacts)
    (defaultTyped : ∀ {statements}, resolution.defaultBody = some statements →
      ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {result : Value}
    (environments : DataHeap.EnvRepresents compilation.checked.catalog mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (evaluated : Evaluates actual store (code.rename ξ) result finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.StatementExecutesOutcome program context evidence source environment before id context outcome after ∧
      OutcomeRepresents model finalMap finalWorld resultSource resultType faults outcome result ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  Certificate.reflects includes
    (certificate_of_lowerWithReasons expressionExtract bodyExtract accepted)
    expressionMeaning bodyMeaning valid found casesTyped defaultTyped environments heaps locals layout evaluated

end Solcore.SourceSemantics.CoreLowering.GenericMatchMeaning
