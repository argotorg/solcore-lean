import Solcore.SourceSemantics.CoreLowering.RecursiveNamedMatchPrefixContracts
import Solcore.SourceSemantics.CoreLowering.CompatiblePatternRuntime

/-! Ordered match selection and actual marked prefixes retain their original
compiler arms, typed slots, binder order and strict native continuation. Numeric
requirements are discharged only from each actual pattern validator and the same
complete runtime ledger. Scrutinee evaluation, entry authority and body execution
remain independent interfaces; no whole Match or Header/Profile closure is claimed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchRuntimeSelection
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly CompatiblePayload
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates DataMatchBranchPrefix
open CallableIndexedHistory CompatibleMatchSelectionPrefix CompatiblePatternExecution CompatibleMatchDecision

abbrev LiteralRows (compilation : CompatiblePatternCertificates.Compilation) (numeric : IntegerLiteralResolution) : Prop :=
  ∃ implementation, NumericLiteralEvidenceReceipts.Selected compilation.solvedRequirements numeric implementation

theorem of_arms {compilation : CompatiblePatternCertificates.Compilation}
    {source site scope expected bodyCertificate cases arms}
    (certificates : Arms compilation source site scope expected bodyCertificate cases arms) :
    CompatibleMatchDecision.Arms.LiteralSites (LiteralRows compilation) certificates :=
  CompatibleMatchDecision.Arms.literalSites certificates _ (fun span expected literal numeric matcher accepted =>
    CompatiblePatternLiteralRuntime.literalMatcher_selected compilation site span expected literal numeric matcher accepted)

theorem of_certificate {compilation : CompatiblePatternCertificates.Compilation}
    {source scope id resolution resultType internalReason expressionCertificate bodyCertificate code}
    (certificate : Certificate compilation source scope id resolution resultType internalReason expressionCertificate bodyCertificate code) :
    CompatibleMatchDecision.Certificate.LiteralSites (LiteralRows compilation) certificate :=
  CompatibleMatchDecision.Certificate.literalSites certificate _ (fun span expected literal numeric matcher accepted =>
    CompatiblePatternLiteralRuntime.literalMatcher_selected compilation id span expected literal numeric matcher accepted)

private theorem requirement {compilation : CompatiblePatternCertificates.Compilation} {context : SourceSemantics.Context}
    (valid : CompatiblePatternRuntime.ContextValid compilation context) {numeric : IntegerLiteralResolution}
    (selected : LiteralRows compilation numeric) : RequirementProves context numeric.requirement numeric.predicate := by
  obtain ⟨implementation, selected⟩ := selected
  exact selected.proves valid.ledger valid.runtime

section
variable {compilation : CompatiblePatternCertificates.Compilation} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
  {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
theorem decides {context : SourceSemantics.Context}
    {source : TypedSource} {site : StatementId} {scope : Scope} {expected : TypeSystem.Ty}
    {bodyCertificate : BodyCertificate} {cases : List TypedMatchCase} {arms : List (Pattern × Expr)}
    {resultType : Ty} {fallback : Option (List StatementId)} {fallbackCode : Expr}
    (certificates : Arms compilation source site scope expected bodyCertificate cases arms)
    (fallbackCertificate : Fallback bodyCertificate scope resultType fallback fallbackCode)
    (valid : CompatiblePatternRuntime.ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world expected sourceValue value payload) :
    ∃ selection, Decision compilation context registry functions mapping world scope bodyCertificate resultType sourceValue value
      cases arms fallback fallbackCode selection :=
  CompatibleMatchDecision.Arms.decides_with_literals certificates fallbackCertificate (LiteralRows compilation) valid.signatures (fun _ selected => requirement valid selected) (of_arms certificates) catalogValid extended represented
end

section
variable {compilation : CompatiblePatternCertificates.Compilation} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
  {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
theorem selects {context : SourceSemantics.Context}
    {source : TypedSource} {site : StatementId} {scope : Scope} {expected : TypeSystem.Ty}
    {bodyCertificate : BodyCertificate} {cases : List TypedMatchCase} {arms : List (Pattern × Expr)}
    {resultType : Ty} {fallback : Option (List StatementId)} {fallbackCode : Expr}
    (certificates : Arms compilation source site scope expected bodyCertificate cases arms)
    (fallbackCertificate : Fallback bodyCertificate scope resultType fallback fallbackCode)
    (valid : CompatiblePatternRuntime.ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value payload)
    {selection : Dynamic.MatchCaseSelection}
    (selected : Dynamic.MatchCasesSelect context sourceValue cases fallback selection) :
    Decision compilation context registry functions mapping world scope bodyCertificate resultType sourceValue value
      cases arms fallback fallbackCode selection :=
  CompatibleMatchSourceSelection.Arms.selects_with_literals certificates fallbackCertificate (LiteralRows compilation) valid.signatures (fun _ selected => requirement valid selected) (of_arms certificates) catalogValid extended represented selected
end

section
variable {compilation : CompatiblePatternCertificates.Compilation} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
  {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
theorem source_selects {context : SourceSemantics.Context}
    {source : TypedSource} {scope : Scope} {id : StatementId} {resolution : MatchResolution}
    {resultType : Ty} {internalReason : Word} {expressionCertificate : ExpressionCertificate}
    {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : CompatibleMatchCertificates.Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code)
    (valid : CompatiblePatternRuntime.ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry) {node : ExpressionNode}
    (found : source.lookupExpression? resolution.scrutinee = some node)
    {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload) :
    ∃ selection, Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection :=
  CompatibleMatchDecision.Certificate.source_selects_with_literals certificate (LiteralRows compilation) valid.signatures (fun _ selected => requirement valid selected) (of_certificate certificate) catalogValid extended found represented
end

theorem selected_prefix
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) (ordinary : Ordinary certificate)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {context : SourceSemantics.Context} (valid : CompatiblePatternRuntime.ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ lowered', expressionCertificate scope resolution.scrutinee lowered' → lowered' = lowered)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store)
    {selection : Dynamic.MatchCaseSelection}
    (selectedSource : Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection)
    {entry : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport entry) (bindings : ProtectedExpressionMeaning.Binds entry)
    (initial : entry scope mapping world heap store canonical) :
    ∃ hiddenHeap location finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore
        finalMap finalWorld finalEmbedding finalContext body,
      Dynamic.Heap.Allocates heap node.type (some sourceValue) location hiddenHeap ∧
      Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection ∧
      SelectedBody bodyCertificate ((resolution.hiddenScrutinee, payload) :: scope) environment hiddenHeap
        resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) finalMap finalWorld administrative
        finalScope finalEnvironment finalCanonical ambient.definitions ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalContext ambient.definitions ∧
      finalCanonical[finalScope.length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      contextLocation ∉ finalMap ∧
      CanonicalPrefix scope canonical finalScope finalCanonical ∧
      entry finalScope finalMap finalWorld finalHeap finalStore finalCanonical ∧
      ContinuationSize true actual before (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) :=
  RecursiveNamedMatchPrefixContracts.selected_prefix_with_literals certificate ordinary onError allocator (LiteralRows compilation) valid.signatures (fun _ selected => requirement valid selected) (of_certificate certificate) catalogValid definitions registered extended found uniqueExpression represented environments heaps agrees actualTyped reference read unmapped evaluated selectedSource transport bindings initial

theorem success_prefix
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) (ordinary : Ordinary certificate)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {context : SourceSemantics.Context} (valid : CompatiblePatternRuntime.ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ lowered', expressionCertificate scope resolution.scrutinee lowered' → lowered' = lowered)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store)
    {entry : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport entry) (bindings : ProtectedExpressionMeaning.Binds entry)
    (initial : entry scope mapping world heap store canonical) :
    ∃ hiddenHeap location selection finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore
        finalMap finalWorld finalEmbedding finalContext body,
      Dynamic.Heap.Allocates heap node.type (some sourceValue) location hiddenHeap ∧
      Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection ∧
      SelectedBody bodyCertificate ((resolution.hiddenScrutinee, payload) :: scope) environment hiddenHeap
        resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) finalMap finalWorld administrative
        finalScope finalEnvironment finalCanonical ambient.definitions ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalContext ambient.definitions ∧
      finalCanonical[finalScope.length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      contextLocation ∉ finalMap ∧
      CanonicalPrefix scope canonical finalScope finalCanonical ∧
      entry finalScope finalMap finalWorld finalHeap finalStore finalCanonical ∧
      ContinuationSize true actual before (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) :=
  RecursiveNamedMatchPrefixContracts.success_prefix_with_literals certificate ordinary onError allocator (LiteralRows compilation) valid.signatures (fun _ selected => requirement valid selected) (of_certificate certificate) catalogValid definitions registered extended found uniqueExpression represented environments heaps agrees actualTyped reference read unmapped evaluated transport bindings initial

end Solcore.SourceSemantics.CoreLowering.CompatibleMatchRuntimeSelection
