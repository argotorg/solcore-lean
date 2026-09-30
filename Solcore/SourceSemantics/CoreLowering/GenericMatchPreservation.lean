import Solcore.SourceSemantics.CoreLowering.DataMatchSourceTrace

/-! Forward finite match correspondence. Child obligations quantify over all
related initial states and finite independent child executions; no evaluator or
termination assumption is introduced. Source allocation determinism identifies
the cells built by the certified Core prefix with the given source trace. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericMatchPreservation
open Core Frontend Frontend.SourceInference GeneralHeap CoreProof ReadOnly
open SourceCoreDataMatches DataMatchCertificates DataMatchBranchPrefix GenericMatchAllocation
open GenericMatchMeaning GenericLexicalContext

/-- Universal child expression preservation, including fault effects. -/
def ExpressionPreserves (compilation : DataPatternCertificates.Compilation)
    (model : GenericHeap.PayloadModel compilation.checked.catalog) (program : Program)
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (certificate : ExpressionCertificate) (faults : FaultRep) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual before store ξ outcome after},
    DataHeap.EnvRepresents compilation.checked.catalog mapping world administrativeContext scope environment canonical →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      ExpressionOutcomeRepresents compilation.checked.catalog compilation.signatures node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

/-- Universal child statement preservation. Independent source static typing
supplies the selected lexical context; source execution supplies finiteness. -/
def BodyPreserves (compilation : DataPatternCertificates.Compilation)
    (model : GenericHeap.PayloadModel compilation.checked.catalog) (program : Program)
    (control : ControlContext) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (certificate : BodyCertificate) (resultSource : TypeSystem.Ty) (resultType : Ty) (faults : FaultRep) : Prop :=
  ∀ {scope statements code}, certificate scope statements code →
  ∀ {context staticFinal facts}, StatementsHaveType source control context statements staticFinal facts →
  ∀ {mapping world administrativeContext environment canonical actual before store ξ finalContext outcome after},
    DataHeap.EnvRepresents compilation.checked.catalog mapping world administrativeContext scope environment canonical →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    Dynamic.StatementsExecuteOutcome program context evidence source environment before statements finalContext outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      OutcomeRepresents model finalMap finalWorld resultSource resultType faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

private theorem allocations_same {before left right : Dynamic.Heap} {type : TypeSystem.Ty} {value : Option Dynamic.Value}
    {a b : Dynamic.Location} (first : Dynamic.Heap.Allocates before type value a left)
    (second : Dynamic.Heap.Allocates before type value b right) : left = right := by
  cases first; cases second; rfl

private theorem binders_same {environment a b : Dynamic.Environment} {before left right : Dynamic.Heap}
    {binders : List TypedBinder} {values : List Dynamic.Value}
    (first : Dynamic.BindersAllocate environment before binders values a left)
    (second : Dynamic.BindersAllocate environment before binders values b right) : a = b ∧ left = right := by
  induction first generalizing b right with
  | nil => cases second; exact ⟨rfl, rfl⟩
  | cons allocation rest ih =>
    cases second with
    | cons allocation' rest' =>
      cases allocation
      cases allocation'
      exact ih rest'

private theorem extensions_same {owner : Resolved.DeclarationId} {context a b : SourceSemantics.Context}
    {binders : List TypedBinder} (first : BindersExtend owner context binders a)
    (second : BindersExtend owner context binders b) : a = b := by
  induction first generalizing b with
  | nil => cases second; rfl
  | cons head tail ih =>
    cases second with
    | cons head' tail' =>
      cases head
      cases head'
      exact ih tail'

private theorem default_selected {context : SourceSemantics.Context} {value : Dynamic.Value}
    {cases : List TypedMatchCase} {fallback : Option (List StatementId)} {statements : List StatementId}
    (selected : Dynamic.MatchCasesSelect context value cases fallback (.default statements)) :
    fallback = some statements := by
  cases selected with
  | default => rfl
  | tail _ next => exact default_selected next
termination_by cases.length
decreasing_by simp_all

/-- A finite independent source match trace yields a finite evaluation of the
actual emitted match code. The source and Core allocate at their own lengths;
the final location map, world and administrative frame remain explicit. -/
theorem Certificate.preserves_trace
    {compilation : DataPatternCertificates.Compilation} {model : GenericHeap.PayloadModel compilation.checked.catalog}
    (includes : IncludesFinite compilation.signatures model)
    {program : Program} {context : SourceSemantics.Context} {control : ControlContext}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultSource : TypeSystem.Ty} {resultType : Ty}
    {internalReason : Word} {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate}
    {faults : FaultRep} {code : Expr}
    (certificate : DataMatchCertificates.Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code)
    (expressionMeaning : ExpressionPreserves compilation model program context evidence source expressionCertificate faults)
    (bodyMeaning : BodyPreserves compilation model program control evidence source bodyCertificate resultSource resultType faults)
    (valid : DataPatternLeaves.ContextValid compilation context) (unique : NodeOccurrencesUnique source)
    {scrutineeNode : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some scrutineeNode)
    {caseFacts : List BodyFacts}
    (casesTyped : MatchCasesHaveType source control context scrutineeNode.type resolution.cases caseFacts)
    (defaultTyped : ∀ {statements}, resolution.defaultBody = some statements →
      ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ControlOutcome}
    (environments : DataHeap.EnvRepresents compilation.checked.catalog mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (trace : DataMatchSourceTrace.Trace program context evidence source environment before resolution outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      OutcomeRepresents model finalMap finalWorld resultSource resultType faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  cases certificate with
  | @matchWith node statementType certifiedNode payload computation arms fallback read allowed form requirements
      hiddenOwned hiddenFresh scrutineeOwned scrutineeFound projection expression sameType armsCertified fallbackCertified =>
    have same := Option.some.inj (found.symm.trans scrutineeFound)
    subst certifiedNode
    cases trace with
    | scrutineeFault fault =>
      obtain ⟨value, finalStore, finalMap, finalWorld, coreEval, related, heapRep, maps, worlds, frame, metadata⟩ :=
        expressionMeaning expression found environments heaps locals layout (.fault fault)
      cases related with
      | fault represented =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault represented, heapRep, maps, worlds, frame, metadata⟩
        rw [LoopRenaming.letInitialized]
        exact LocalSequence.letInitialized_failure _ _ (by simpa only [← sameType] using coreEval)
    | patternFault contains evaluated allocated fault =>
      exact False.elim (GenericMatchSelection.Arms.not_pattern_fault armsCertified valid _ fault)
    | @arm sourceNode sourceValue middle hidden location statements bindings armContext armEnvironment bound
        innerFinal innerOutcome sourceAfter contains sourceEval sourceHidden selected sourceExtended sourceAllocated sourceBody =>
      have nodeEq : sourceNode = scrutineeNode := Option.some.inj
        ((lookupExpression?_complete unique contains).symm.trans found)
      subst sourceNode
      obtain ⟨value, middleStore, middleMap, middleWorld, coreEval, represented, middleRelated,
        firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        expressionMeaning expression found environments heaps locals layout (.value sourceEval)
      cases represented with
      | value represented =>
        obtain ⟨hiddenHeap, hiddenLocation, finalScope, selectedEnvironment, selectedHeap, selectedCanonical,
          selectedActual, selectedStore, selectedMap, selectedWorld, selectedEmbedding, body,
          hiddenAllocated, selectedAgain, selectedBody, selectedEnv, selectedRelated, secondMaps, secondWorlds,
          secondFrame, selectedLayout, agreement⟩ :=
          GenericMatchSelectedPrefix.selected_prefix includes hiddenFresh (DataPatternBindings.projected_raw projection)
            armsCertified fallbackCertified valid represented (environments.extend firstMaps firstWorlds)
            middleRelated layout coreEval selected
        have hiddenEq := allocations_same hiddenAllocated sourceHidden
        subst hiddenHeap
        cases selectedBody with
        | arm binders allocated bodyCertified =>
          obtain ⟨sameEnvironment, sameHeap⟩ := binders_same allocated sourceAllocated
          subst selectedEnvironment
          subst selectedHeap
          obtain ⟨staticContext, staticFinal, facts, extended, typed, _⟩ :=
            DataMatchSourceScopes.MatchCasesSelect.arm_scope casesTyped selected
          have sameContext := extensions_same extended sourceExtended
          subst staticContext
          obtain ⟨result, finalStore, finalMap, finalWorld, bodyEval, related, finalHeapRep,
            thirdMaps, thirdWorlds, thirdFrame, thirdMetadata⟩ :=
            bodyMeaning bodyCertified typed selectedEnv selectedRelated
              (binders_agree sourceExtended (arm_monomorphic casesTyped selected)
                (locals.mono (firstMetadata.trans (.of_allocation sourceHidden))) sourceAllocated)
              selectedLayout sourceBody
          exact ⟨result, finalStore, finalMap, finalWorld, agreement.wrap bodyEval, related.restore environment,
            finalHeapRep, firstMaps.trans (secondMaps.trans thirdMaps), firstWorlds.trans (secondWorlds.trans thirdWorlds),
            firstFrame.trans (secondFrame.trans thirdFrame),
            firstMetadata.trans ((Dynamic.HeapMetadataExtend.of_allocation sourceHidden).trans
              ((binders_metadata sourceAllocated).trans thirdMetadata))⟩
    | @default sourceNode sourceValue middle hidden location statements innerFinal innerOutcome sourceAfter
        contains sourceEval sourceHidden selected sourceBody =>
      have nodeEq : sourceNode = scrutineeNode := Option.some.inj
        ((lookupExpression?_complete unique contains).symm.trans found)
      subst sourceNode
      obtain ⟨value, middleStore, middleMap, middleWorld, coreEval, represented, middleRelated,
        firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        expressionMeaning expression found environments heaps locals layout (.value sourceEval)
      cases represented with
      | value represented =>
        obtain ⟨hiddenHeap, hiddenLocation, finalScope, selectedEnvironment, selectedHeap, selectedCanonical,
          selectedActual, selectedStore, selectedMap, selectedWorld, selectedEmbedding, body,
          hiddenAllocated, selectedAgain, selectedBody, selectedEnv, selectedRelated, secondMaps, secondWorlds,
          secondFrame, selectedLayout, agreement⟩ :=
          GenericMatchSelectedPrefix.selected_prefix includes hiddenFresh (DataPatternBindings.projected_raw projection)
            armsCertified fallbackCertified valid represented (environments.extend firstMaps firstWorlds)
            middleRelated layout coreEval selected
        have hiddenEq := allocations_same hiddenAllocated sourceHidden
        subst hiddenHeap
        cases selectedBody with
        | default bodyCertified =>
          obtain ⟨staticFinal, facts, typed⟩ := defaultTyped (default_selected selected)
          obtain ⟨result, finalStore, finalMap, finalWorld, bodyEval, related, finalHeapRep,
            thirdMaps, thirdWorlds, thirdFrame, thirdMetadata⟩ :=
            bodyMeaning bodyCertified typed selectedEnv selectedRelated
              (locals.mono (firstMetadata.trans (.of_allocation sourceHidden))) selectedLayout sourceBody
          exact ⟨result, finalStore, finalMap, finalWorld, agreement.wrap bodyEval, related.restore environment,
            finalHeapRep, firstMaps.trans (secondMaps.trans thirdMaps), firstWorlds.trans (secondWorlds.trans thirdWorlds),
            firstFrame.trans (secondFrame.trans thirdFrame),
            firstMetadata.trans ((Dynamic.HeapMetadataExtend.of_allocation sourceHidden).trans thirdMetadata)⟩
    | @noBranch sourceNode sourceValue middle hidden location contains sourceEval sourceHidden selected =>
      have nodeEq : sourceNode = scrutineeNode := Option.some.inj
        ((lookupExpression?_complete unique contains).symm.trans found)
      subst sourceNode
      obtain ⟨value, middleStore, middleMap, middleWorld, coreEval, represented, middleRelated,
        firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        expressionMeaning expression found environments heaps locals layout (.value sourceEval)
      cases represented with
      | value represented =>
        obtain ⟨hiddenHeap, hiddenLocation, finalScope, selectedEnvironment, selectedHeap, selectedCanonical,
          selectedActual, selectedStore, selectedMap, selectedWorld, selectedEmbedding, body,
          hiddenAllocated, selectedAgain, selectedBody, selectedEnv, selectedRelated, secondMaps, secondWorlds,
          secondFrame, selectedLayout, agreement⟩ :=
          GenericMatchSelectedPrefix.selected_prefix includes hiddenFresh (DataPatternBindings.projected_raw projection)
            armsCertified fallbackCertified valid represented (environments.extend firstMaps firstWorlds)
            middleRelated layout coreEval selected
        have hiddenEq := allocations_same hiddenAllocated sourceHidden
        subst hiddenHeap
        cases selectedBody
        exact ⟨_, selectedStore, selectedMap, selectedWorld, agreement.wrap (.inRight (.inLeft (.inLeft .unit))),
          .fallthrough environment, selectedRelated, firstMaps.trans secondMaps, firstWorlds.trans secondWorlds,
          firstFrame.trans secondFrame, firstMetadata.trans (.of_allocation sourceHidden)⟩

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


/-- The independent statement-outcome judgment supplies the finite trace;
its view is derived using occurrence uniqueness rather than assumed. -/
theorem Certificate.preserves
    {compilation : DataPatternCertificates.Compilation} {model : GenericHeap.PayloadModel compilation.checked.catalog}
    (includes : IncludesFinite compilation.signatures model)
    {program : Program} {context : SourceSemantics.Context} {control : ControlContext}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultSource : TypeSystem.Ty} {resultType : Ty}
    {internalReason : Word} {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate}
    {faults : FaultRep} {code : Expr}
    (certificate : DataMatchCertificates.Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code)
    (expressionMeaning : ExpressionPreserves compilation model program context evidence source expressionCertificate faults)
    (bodyMeaning : BodyPreserves compilation model program control evidence source bodyCertificate resultSource resultType faults)
    (valid : DataPatternLeaves.ContextValid compilation context) (unique : NodeOccurrencesUnique source)
    {scrutineeNode : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some scrutineeNode)
    {caseFacts : List BodyFacts}
    (casesTyped : MatchCasesHaveType source control context scrutineeNode.type resolution.cases caseFacts)
    (defaultTyped : ∀ {statements}, resolution.defaultBody = some statements →
      ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ControlOutcome} {finalContext : SourceSemantics.Context}
    (environments : DataHeap.EnvRepresents compilation.checked.catalog mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (executed : Dynamic.StatementExecutesOutcome program context evidence source environment before id finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      OutcomeRepresents model finalMap finalWorld resultSource resultType faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  have view : DataMatchSourceTrace.Trace program context evidence source environment before resolution outcome after := by
    cases certificate with
    | matchWith read allowed form => exact (DataMatchSourceTrace.of_outcome unique (read_contains read) form executed).2
  exact Certificate.preserves_trace includes certificate expressionMeaning bodyMeaning valid unique found casesTyped
    defaultTyped environments heaps locals layout view

/-- Actual accepted match lowering preserves each independently finite source
outcome, under explicit universal child compiler correspondence theorems. -/
theorem lowerWithReasons_preserves
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
    (expressionMeaning : ExpressionPreserves compilation model program context evidence source expressionCertificate faults)
    (bodyMeaning : BodyPreserves compilation model program control evidence source bodyCertificate resultSource resultType faults)
    (valid : DataPatternLeaves.ContextValid compilation context) (unique : NodeOccurrencesUnique source)
    {scrutineeNode : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some scrutineeNode)
    {caseFacts : List BodyFacts}
    (casesTyped : MatchCasesHaveType source control context scrutineeNode.type resolution.cases caseFacts)
    (defaultTyped : ∀ {statements}, resolution.defaultBody = some statements →
      ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ControlOutcome} {finalContext : SourceSemantics.Context}
    (environments : DataHeap.EnvRepresents compilation.checked.catalog mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (executed : Dynamic.StatementExecutesOutcome program context evidence source environment before id finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      OutcomeRepresents model finalMap finalWorld resultSource resultType faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  Certificate.preserves includes (certificate_of_lowerWithReasons expressionExtract bodyExtract accepted)
    expressionMeaning bodyMeaning valid unique found casesTyped defaultTyped environments heaps locals layout executed

end Solcore.SourceSemantics.CoreLowering.GenericMatchPreservation
