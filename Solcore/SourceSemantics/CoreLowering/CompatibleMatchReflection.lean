import Solcore.SourceSemantics.CoreLowering.RecursiveNamedMatchSourceBounds

/-! Completed actual compatible match evaluation constructs the independent
source scrutinee, ordered selection, selected body and restored control. The
runtime frame and actual captures are produced by the marked prefix itself. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchReflection
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates CompatibleMatchMeaning
open DataMatchBranchPrefix GenericLexicalContext CallableIndexedHistory
open TypedLexicalWhile (FlowRep Restored restored restore_rep)

private theorem read_contains {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource}
    {id : StatementId} {node : StatementNode} {type : Ty}
    (read : SourceCoreCompatibleDataExpressions.readStatement checked source id = .ok (node, type)) :
    ContainsStatement source id node := by
  by_cases owned : id.occurrence.owner = source.owner
  · simp only [SourceCoreCompatibleDataExpressions.readStatement, owned, ne_eq, not_true_eq_false, ↓reduceIte,
      pure, Except.pure, bind, Except.bind] at read
    cases found : source.lookupStatement? id with
    | none => simp [found] at read
    | some selected =>
      simp only [found] at read
      cases projected : SourceCoreCompatibleDataExpressions.projectType checked (.occurrence id.occurrence) selected.type with
      | error => simp [projected] at read
      | ok projectedType =>
        simp only [projected, Except.ok.injEq, Prod.mk.injEq] at read
        rcases read with ⟨rfl, rfl⟩
        exact lookupStatement?_sound found
  · simp [SourceCoreCompatibleDataExpressions.readStatement, owned, bind, Except.bind] at read

private theorem default_selected {context : SourceSemantics.Context} {value : Dynamic.Value}
    {cases : List TypedMatchCase} {fallback : Option (List StatementId)} {statements : List StatementId}
    (selected : Dynamic.MatchCasesSelect context value cases fallback (.default statements)) :
    fallback = some statements := by
  cases selected with
  | default => rfl
  | tail _ next => exact default_selected next
termination_by cases.length
decreasing_by simp_all

theorem Certificate.reflects_bounded_for
    {compilation : SourceCoreCompatibleDataMatches.Context}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    (functions : FunctionModel compilation.checked.catalog ambient)
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    {registry : SourceCoreRawMetadata.Registry}
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {source : TypedSource} {context : SourceSemantics.Context} {control : ControlContext}
    {program : Program} {evidence : Dynamic.EvidenceEnvironment} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {expected : TypeSystem.Ty} {type : Ty} {reason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : CompatibleMatchCertificates.Certificate compilation source scope id resolution type reason
      expressionCertificate bodyCertificate code)
    (ordinary : CompatibleMatchSelectionPrefix.Ordinary certificate)
    (validity : SourceSemantics.Context → Prop)
    (literals : IntegerLiteralResolution → Prop)
    (signatures : context.signatures = compilation.signatures)
    (numericRequirements : ∀ numeric, literals numeric → RequirementProves context numeric.requirement numeric.predicate)
    (sites : CompatibleMatchDecision.Certificate.LiteralSites literals certificate)
    (validity_binders : ∀ {binders target}, BindersExtend source.owner context binders target →
      validity context → validity target)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ other, expressionCertificate scope resolution.scrutinee other → other = lowered)
    {caseFacts : List BodyFacts}
    (casesTyped : MatchCasesHaveType source control context node.type resolution.cases caseFacts)
    (defaultTyped : ∀ {statements}, resolution.defaultBody = some statements →
      ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts)
    {administrative : Core.Context} {faults : FunctionCalls.FaultRep}
    (budget size : Nat) (bounded : size ≤ budget) {entry : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport entry) (entryBindings : ProtectedExpressionMeaning.Binds entry)
    (expressionMeaning : validity context →
      ∀ child, child < budget → RecursiveNamedBoundedContracts.ReflectsAt child (CompatibleAmbientHeap.payloadModel compilation.checked registry functions)
        program context evidence source expressionCertificate faults entry)
    (armMeaning : RecursiveNamedMatchSourceBounds.ArmReflectsBelowFor (entry := entry) functions program context control evidence resolution bodyCertificate expected type budget validity scope
      (source := source) (administrative := administrative) (frame := frame) (globals := globals)
      (registry := registry) (faults := faults))
    (defaultMeaning : RecursiveNamedMatchSourceBounds.DefaultReflectsBelowFor (entry := entry) functions program context control evidence resolution bodyCertificate expected type budget validity scope
      (source := source) (administrative := administrative) (frame := frame) (globals := globals)
      (registry := registry) (faults := faults)) :
    RecursiveNamedMatchSourceBounds.Head.HeadReflectsAtFor (entry := entry) functions program evidence validity (values := compilation.values) (source := source)
      (context := context) (administrative := administrative) (frameLayout := frame)
      (globals := globals) (registry := registry) (faults := faults) size (scope := scope) id expected type code := by
  intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native result
    environments heaps locals agrees actualTyped reference read unmapped initial completed
  have fullCertificate := certificate
  cases certificate with
  | matchWith readStatement allowed form requirements hiddenOwned hiddenFresh scrutineeOwned scrutineeFound projection
      expression sameType arms fallback branches hiddenCompiled =>
    have contains := read_contains readStatement
    obtain ⟨childNode, child, childSize, value, middleStore, childFound, childCertificate, childSmaller, childCompleted⟩ :=
      RecursiveNamedMatchSourceBounds.Certificate.initial_evaluation_sized fullCertificate completed
    have childEq := uniqueExpression _ childCertificate
    subst child
    have nodeEq := Option.some.inj (found.symm.trans childFound)
    subst childNode
    obtain ⟨sourceSize, sourceOutcome, middleHeap, middleMap, middleWorld, sourceEval, represented,
      middleRelated, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
      expressionMeaning contextValid childSize (Nat.lt_of_lt_of_le childSmaller bounded) childCertificate found environments heaps locals agrees actualTyped initial childCompleted
    cases represented with
    | @fault reason token matched =>
      cases sourceEval with
      | fault sourceFault =>
        have failed := CompatibleMatchScrutineeReflection.Certificate.failure_preserves fullCertificate uniqueExpression childCompleted.sound
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound failed
        have sourceMatch : Dynamic.StatementExecutesOutcome program context evidence source environment before id context (.fault reason) middleHeap :=
          .fault (.matchScrutinee contains form sourceFault.sound)
        obtain ⟨wholeSourceSize, measured⟩ := RecursiveNamedLoopContracts.StatementOutcome.has_size sourceMatch
        exact ⟨wholeSourceSize, .fault reason, middleHeap, middleMap, middleWorld,
          measured, (by intro next impossible; cases impossible),
          .fault matched, middleRelated, firstMaps, firstWorlds, firstFrame, firstMetadata⟩
    | @value sourceValue value payload =>
      cases sourceEval with
      | value sourceEval =>
        obtain ⟨stillUnmapped, stillRead⟩ := firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1
        obtain ⟨hiddenHeap, location, selection, finalScope, selectedEnvironment, selectedHeap, selectedCanonical,
          selectedActual, selectedStore, selectedMap, selectedWorld, selectedEmbedding, selectedContext, body,
          hiddenAllocated, selected, selectedBody, selectedEnv, selectedRelated, secondMaps, secondWorlds, secondFrame,
          selectedLayout, selectedTyped, selectedReference, selectedRead, selectedUnmapped, spine, selectedEntry, agreement⟩ :=
          RecursiveNamedMatchPrefixContracts.success_prefix_with_literals fullCertificate ordinary onError allocator literals signatures numericRequirements sites
            catalogValid definitions registered extended found uniqueExpression payload (environments.extend firstMaps firstWorlds)
            middleRelated agrees (actualTyped.weaken firstWorlds) reference (stillRead.trans read) stillUnmapped childCompleted.sound transport entryBindings
            (transport.extend initial firstMaps firstWorlds firstFrame firstMetadata)
        obtain ⟨bodySize, bodySmaller, bodyEval⟩ := agreement.remaining completed
        cases selectedBody with
        | @arm statements bindings compiledBindings finalEnvironment finalHeap body binders allocated certified =>
          obtain ⟨armContext, staticFinal, facts, extendedContext, typed, _⟩ :=
            DataMatchSourceScopes.MatchCasesSelect.arm_scope casesTyped selected
          obtain ⟨bodySourceSize, finalContext, outcome, after, finalMap, finalWorld, sourceBody, related,
            finalHeaps, thirdMaps, thirdWorlds, thirdFrame, thirdMetadata, lexical⟩ :=
            armMeaning rfl selected (.arm binders allocated certified) extendedContext typed bodySize (Nat.lt_of_lt_of_le bodySmaller bounded)
              (validity_binders extendedContext contextValid) selectedEnv selectedRelated
              (binders_agree extendedContext (arm_monomorphic casesTyped selected)
                (locals.mono (firstMetadata.trans (.of_allocation hiddenAllocated))) allocated)
              selectedLayout selectedTyped selectedReference selectedRead selectedUnmapped selectedEntry bodyEval
          have sourceMatch := (DataMatchSourceTrace.Trace.arm (lookupExpression?_sound found) sourceEval.sound hiddenAllocated
            selected extendedContext allocated sourceBody.sound).statement contains form
          obtain ⟨wholeSourceSize, measured⟩ := RecursiveNamedLoopContracts.StatementOutcome.has_size sourceMatch
          exact ⟨wholeSourceSize, _, after, finalMap, finalWorld, measured, restored environment outcome, restore_rep related environment,
            finalHeaps, firstMaps.trans (secondMaps.trans thirdMaps), firstWorlds.trans (secondWorlds.trans thirdWorlds),
            firstFrame.trans (secondFrame.trans thirdFrame), firstMetadata.trans
              ((Dynamic.HeapMetadataExtend.of_allocation hiddenAllocated).trans ((binders_metadata allocated).trans thirdMetadata))⟩
        | @default statements body certified =>
          obtain ⟨staticFinal, facts, typed⟩ := defaultTyped (default_selected selected)
          obtain ⟨bodySourceSize, finalContext, outcome, after, finalMap, finalWorld, sourceBody, related,
            finalHeaps, thirdMaps, thirdWorlds, thirdFrame, thirdMetadata, lexical⟩ :=
            defaultMeaning (environment := environment) (heap := hiddenHeap) rfl selected (.default certified) typed bodySize (Nat.lt_of_lt_of_le bodySmaller bounded) contextValid selectedEnv selectedRelated
              (locals.mono (firstMetadata.trans (.of_allocation hiddenAllocated))) selectedLayout selectedTyped
              selectedReference selectedRead selectedUnmapped selectedEntry bodyEval
          have sourceMatch := (DataMatchSourceTrace.Trace.default (lookupExpression?_sound found) sourceEval.sound hiddenAllocated
            selected sourceBody.sound).statement contains form
          obtain ⟨wholeSourceSize, measured⟩ := RecursiveNamedLoopContracts.StatementOutcome.has_size sourceMatch
          exact ⟨wholeSourceSize, _, after, finalMap, finalWorld, measured, restored environment outcome, restore_rep related environment,
            finalHeaps, firstMaps.trans (secondMaps.trans thirdMaps), firstWorlds.trans (secondWorlds.trans thirdWorlds),
            firstFrame.trans (secondFrame.trans thirdFrame), firstMetadata.trans
              ((Dynamic.HeapMetadataExtend.of_allocation hiddenAllocated).trans thirdMetadata)⟩
        | noBranch =>
          have finished : Evaluates selectedActual selectedStore ((LocalLoop.fallthrough type).rename selectedEmbedding)
              (LocalLoop.fallthroughValue type) selectedStore := .inRight (.inLeft (.inLeft .unit))
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic bodyEval.sound finished
          have sourceMatch : Dynamic.StatementExecutesOutcome program context evidence source environment before id context (.fallthrough environment) hiddenHeap :=
            .control (.matchNoBranch contains form (lookupExpression?_sound found) sourceEval.sound hiddenAllocated selected)
          obtain ⟨wholeSourceSize, measured⟩ := RecursiveNamedLoopContracts.StatementOutcome.has_size sourceMatch
          exact ⟨wholeSourceSize, .fallthrough environment, hiddenHeap, selectedMap, selectedWorld, measured,
            (by intro next same; exact Dynamic.ControlOutcome.fallthrough.inj same.symm),
            .fallthrough environment, selectedRelated, firstMaps.trans secondMaps, firstWorlds.trans secondWorlds,
            firstFrame.trans secondFrame, firstMetadata.trans (.of_allocation hiddenAllocated)⟩



theorem Certificate.reflects_bounded
    {compilation : SourceCoreCompatibleDataMatches.Context}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    (functions : FunctionModel compilation.checked.catalog ambient)
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    {registry : SourceCoreRawMetadata.Registry}
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {source : TypedSource} {context : SourceSemantics.Context} {control : ControlContext}
    {program : Program} {evidence : Dynamic.EvidenceEnvironment} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {expected : TypeSystem.Ty} {type : Ty} {reason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : CompatibleMatchCertificates.Certificate compilation source scope id resolution type reason
      expressionCertificate bodyCertificate code)
    (ordinary : CompatibleMatchSelectionPrefix.Ordinary certificate)
    (valid : CompatiblePatternLeaves.ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ other, expressionCertificate scope resolution.scrutinee other → other = lowered)
    {caseFacts : List BodyFacts}
    (casesTyped : MatchCasesHaveType source control context node.type resolution.cases caseFacts)
    (defaultTyped : ∀ {statements}, resolution.defaultBody = some statements →
      ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts)
    {solved : List SolvedRequirement} {administrative : Core.Context} {faults : FunctionCalls.FaultRep}
    (budget size : Nat) (bounded : size ≤ budget) {entry : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport entry) (entryBindings : ProtectedExpressionMeaning.Binds entry)
    (expressionMeaning : CompatibleExpressionLiterals.ContextValid solved context evidence →
      ∀ child, child < budget → RecursiveNamedBoundedContracts.ReflectsAt child (CompatibleAmbientHeap.payloadModel compilation.checked registry functions)
        program context evidence source expressionCertificate faults entry)
    (armMeaning : RecursiveNamedMatchSourceBounds.ArmReflectsBelow (entry := entry) functions program context control evidence resolution bodyCertificate expected type budget scope
      (source := source) (solved := solved) (administrative := administrative) (frame := frame) (globals := globals)
      (registry := registry) (faults := faults))
    (defaultMeaning : RecursiveNamedMatchSourceBounds.DefaultReflectsBelow (entry := entry) functions program context control evidence resolution bodyCertificate expected type budget scope
      (source := source) (solved := solved) (administrative := administrative) (frame := frame) (globals := globals)
      (registry := registry) (faults := faults)) :
    RecursiveNamedMatchSourceBounds.Head.HeadReflectsAt (entry := entry) functions program evidence (values := compilation.values) (source := source)
      (context := context) (solved := solved) (administrative := administrative) (frameLayout := frame)
      (globals := globals) (registry := registry) (faults := faults) size (scope := scope) id expected type code := by
  exact Certificate.reflects_bounded_for onError allocator functions definitions registered extended certificate ordinary (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) _ valid.signatures
    (fun _ proof => proof) (CompatibleMatchDecision.Certificate.ordinary_sites certificate valid)
    (fun extended proof => valid_binders evidence proof extended) catalogValid
    found uniqueExpression casesTyped defaultTyped budget size bounded transport entryBindings expressionMeaning armMeaning defaultMeaning

theorem Certificate.reflects_scoped
    {compilation : SourceCoreCompatibleDataMatches.Context}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    (functions : FunctionModel compilation.checked.catalog ambient)
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    {registry : SourceCoreRawMetadata.Registry}
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {source : TypedSource} {context : SourceSemantics.Context} {control : ControlContext}
    {program : Program} {evidence : Dynamic.EvidenceEnvironment} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {expected : TypeSystem.Ty} {type : Ty} {reason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : CompatibleMatchCertificates.Certificate compilation source scope id resolution type reason
      expressionCertificate bodyCertificate code)
    (ordinary : CompatibleMatchSelectionPrefix.Ordinary certificate)
    (valid : CompatiblePatternLeaves.ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ other, expressionCertificate scope resolution.scrutinee other → other = lowered)
    {caseFacts : List BodyFacts}
    (casesTyped : MatchCasesHaveType source control context node.type resolution.cases caseFacts)
    (defaultTyped : ∀ {statements}, resolution.defaultBody = some statements →
      ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts)
    {solved : List SolvedRequirement} {administrative : Core.Context} {faults : FunctionCalls.FaultRep}
    (expressionMeaning : CompatibleExpressionLiterals.ContextValid solved context evidence →
      TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel compilation.checked registry functions)
        program context evidence source expressionCertificate faults)
    (armMeaning : ArmReflectsScoped functions program context control evidence resolution bodyCertificate expected type scope
      (source := source) (solved := solved) (administrative := administrative) (frame := frame) (globals := globals)
      (registry := registry) (faults := faults))
    (defaultMeaning : DefaultReflectsScoped functions program context control evidence resolution bodyCertificate expected type scope
      (source := source) (solved := solved) (administrative := administrative) (frame := frame) (globals := globals)
      (registry := registry) (faults := faults)) :
    TypedLexicalWhile.HeadReflects functions program evidence (values := compilation.values) (source := source)
      (context := context) (solved := solved) (administrative := administrative) (frameLayout := frame)
      (globals := globals) (registry := registry) (faults := faults) (scope := scope) id expected type code := by
  intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native result
    environments heaps locals agrees actualTyped reference read unmapped completed
  obtain ⟨size, measured⟩ := evaluation_has_size completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, traced, restores, related, finalHeaps, maps, worlds, preserved, metadata⟩ :=
    Certificate.reflects_bounded onError allocator functions definitions registered extended certificate ordinary valid catalogValid
      found uniqueExpression casesTyped defaultTyped size size (Nat.le_refl _) (entry := fun _ _ _ _ _ _ => True)
      ⟨by intros; trivial⟩ ⟨by intros; trivial, by intros; trivial⟩
      (by
        intro contextValid child smaller scope id lowered certified node found mapping world administrative environment canonical actual actualContext before store ξ value finalStore environments heaps locals agrees typed installed evaluated
        obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
          expressionMeaning contextValid certified found environments heaps locals agrees typed evaluated.sound
        obtain ⟨sourceSize, measured⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size trace
        exact ⟨sourceSize, outcome, after, finalMap, finalWorld, measured, represented, finalHeaps, maps, worlds, frame, metadata⟩)
      (RecursiveNamedMatchSourceBounds.ArmReflectsBelow.of_unbounded size armMeaning)
      (RecursiveNamedMatchSourceBounds.DefaultReflectsBelow.of_unbounded size defaultMeaning)
      contextValid environments heaps locals agrees actualTyped reference read unmapped True.intro measured
  exact ⟨outcome, after, finalMap, finalWorld, traced.sound, restores, related, finalHeaps, maps, worlds, preserved, metadata⟩

theorem Certificate.reflects
    {compilation : SourceCoreCompatibleDataMatches.Context}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    (functions : FunctionModel compilation.checked.catalog ambient)
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    {registry : SourceCoreRawMetadata.Registry}
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {source : TypedSource} {context : SourceSemantics.Context} {control : ControlContext}
    {program : Program} {evidence : Dynamic.EvidenceEnvironment} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {expected : TypeSystem.Ty} {type : Ty} {reason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : CompatibleMatchCertificates.Certificate compilation source scope id resolution type reason
      expressionCertificate bodyCertificate code)
    (ordinary : CompatibleMatchSelectionPrefix.Ordinary certificate)
    (valid : CompatiblePatternLeaves.ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ other, expressionCertificate scope resolution.scrutinee other → other = lowered)
    {caseFacts : List BodyFacts}
    (casesTyped : MatchCasesHaveType source control context node.type resolution.cases caseFacts)
    (defaultTyped : ∀ {statements}, resolution.defaultBody = some statements →
      ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts)
    {solved : List SolvedRequirement} {administrative : Core.Context} {faults : FunctionCalls.FaultRep}
    (expressionMeaning : CompatibleExpressionLiterals.ContextValid solved context evidence →
      TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel compilation.checked registry functions)
        program context evidence source expressionCertificate faults)
    (armMeaning : ArmReflects functions program context control evidence resolution bodyCertificate expected type
      (source := source) (solved := solved) (administrative := administrative) (frame := frame) (globals := globals)
      (registry := registry) (faults := faults))
    (defaultMeaning : DefaultReflects functions program context control evidence resolution bodyCertificate expected type
      (source := source) (solved := solved) (administrative := administrative) (frame := frame) (globals := globals)
      (registry := registry) (faults := faults)) :
    TypedLexicalWhile.HeadReflects functions program evidence (values := compilation.values) (source := source)
      (context := context) (solved := solved) (administrative := administrative) (frameLayout := frame)
      (globals := globals) (registry := registry) (faults := faults) (scope := scope) id expected type code := by
  exact Certificate.reflects_scoped onError allocator functions definitions registered extended certificate ordinary valid catalogValid
    found uniqueExpression casesTyped defaultTyped expressionMeaning (armMeaning.scoped scope) (defaultMeaning.scoped scope)

end Solcore.SourceSemantics.CoreLowering.CompatibleMatchReflection
