import Solcore.SourceSemantics.CoreLowering.Internal.Selected.IndirectDispatch
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.Builtins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalCellOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.CatalogOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.NamedAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalNamedCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.ExpressionBounds
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.IndexBounds
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.IndexDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.MethodBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.CallerMethodSelection
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.RecursiveCallerCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MixedClosures
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.SelectedGeneralCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.ExpressionBounds
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.DirectCallers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCallerSlotForgetting
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExpressionHeads

/-!
# Selected compilations: direct calls

Bounds of direct calls and raw direct calls in a selected compilation, with their argument rows and Source types, and the caller bounds they share.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationGlobalCallPrefixes
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationGlobalCallPrefixes
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedStagedIndirectNativePrefix (CalleePost)
open CallableIndexedOwnedPreparedStagedIndirectBuiltinPreservationDispatch (ParentAt)
open CallableIndexedOwnedPreparedScopedCallBoundaryReceipts (CallView)
open CallableIndexedOwnedContextualCalleeStageReceipts (BoundaryAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  {sourceTypes : List TypeSystem.Ty} {calleeNode : ExpressionNode}
  {sidecar : SourceCoreStageContracts.Sidecar}

variable {functionModel : FunctionModel compiled.compatible.checked.catalog
  (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
local notation "functions" => functionModel
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics


/-- The uncompleted named branch retains the actual global value, all three
Source prefixes and application suffix, and every native prefix witness. -/
def GlobalAppliedPrefix (calleeSize argumentsSize applicationSize : Nat)
    (sourceValue : Dynamic.Value) (calleeHeap argumentsHeap : Dynamic.Heap)
    (sources : List Dynamic.Value) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ function : Dynamic.GlobalFunction,
    sourceValue = .global function ∧
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value sourceValue) calleeHeap ∧
    Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue ∧
    Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap ∧
    Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages applicationSize
      invocation context argumentsHeap sourceValue sources outcome after ∧
    SelectedCompilationIndirectValuesPrefix.ValuesPrefix (functionModel := functions)
      (registry := completion.result.context.registry) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial sourceValue calleeHeap argumentsHeap sources

/-- This remaining branch retains the actual global value and complete
original user prefix. It supplies no named application or body meaning. -/
def GlobalApplicationPrefix (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  ∃ function : Dynamic.GlobalFunction,
    ∃ rawParameter rawResult,
      calleeNode.type = .function rawParameter rawResult ∧
      TypeSystem.Ty.productMany sourceTypes = rawParameter ∧ compiler.original.type = rawResult ∧
    ∃ calleeSize argumentsSize calleeHeap calleeStore calleeMap calleeWorld sources values carrier
        argumentsHeap argumentsStore finalMap finalWorld originalNode originalMetadata,
      CallableIndexedOwnedPreparedStagedIndirectNativePrefix.CalleePost
        (registry := completion.result.context.registry) (context := context) (actual := actual)
        (ξ := ξ) (calleeNode := calleeNode) bridge functions compiler initial
        (.global function) calleeHeap carrier calleeStore calleeMap calleeWorld ∧
      Dynamic.ValueHasType context calleeHeap (.global function) calleeNode.type ∧
      Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
        invocation context environment before callee (.value (.global function)) calleeHeap ∧
      Staging.CallBoundary.GuardAccepts invocation.guards id ids (.global function) ∧
      Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
        invocation context environment calleeHeap ids (.values sources) argumentsHeap ∧
      DataExpressionSequence.Values model finalMap finalWorld sourceTypes (compiler.codes.map (·.type)) sources values ∧
      GenericHeap.PayloadModel.Represents model finalMap finalWorld calleeNode.type
        (.global function) carrier compiler.calleeCode.type ∧
      CallableIndexedOwnedPreparedScopedCallBoundaryReceipts.CallView originalNode compiler.original originalMetadata metadata ∧
      CallableIndexedOwnedContextualCalleeStageReceipts.BoundaryAt
        sidecar prepared.site callee ids originalMetadata originalNode (.global function) carrier ∧
      GenericHeap.HeapRepresents model finalMap finalWorld argumentsHeap argumentsStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap argumentsStore ∧ Dynamic.HeapMetadataExtend before argumentsHeap ∧
      Dynamic.ValuesHaveTypes context argumentsHeap sources sourceTypes ∧
      Dynamic.HeapMetadataExtend calleeHeap argumentsHeap ∧
      (∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, argumentsHeap, argumentsStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Admission bridge context reached) ∧
      ∃ suffixSize, EvaluationSize suffixSize (DataPatternValues.packValues values :: .unit :: carrier :: actual)
        argumentsStore
        (LanguageResult.bind compiler.resultType
          (CallableContract.dispatch prepared.site.gates .beforeApplication
            compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown (.second (.var 2)))
          (.apply (.second (.first (.var 3))) (.var 1))) value finalStore ∧ suffixSize < budget

/-- The remaining named branch carries the same original parent size and a
strict actual Source application child, alongside all original prefix receipts. -/
def GlobalAt (budget size : Nat) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ calleeSize argumentsSize applicationSize sourceValue calleeHeap argumentsHeap sources,
    size = Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, applicationSize] ∧
    applicationSize < budget ∧
    GlobalAppliedPrefix (functionModel := functionModel) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes) (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial calleeSize argumentsSize applicationSize sourceValue
      calleeHeap argumentsHeap sources outcome after


end Solcore.SourceSemantics.CoreLowering.SelectedCompilationGlobalCallPrefixes
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationDirectSourceTypes
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationDirectSourceTypes
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Receipt)
open CallableIndexedOwnedPreparedStagedDirectCallAuthority (Ready)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {values : SourceCoreCompatibleValues.Context}
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr} {program : Program}
  (receipt : Receipt policy body fuel compilation values source scope id callee ids instantiation reasonAt lowered)

theorem source_types
    {catalog : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
    (ready : Ready receipt catalog) {context : SourceSemantics.Context}
    {types : List TypeSystem.Ty}
    (shaped : SelectedCompilationSourceSignatureFacts.Shape ready.header)
    (signatures : context.signatures = program.signatures)
    (application : DeclarationApplicationValid context instantiation types
      receipt.node.type instantiation.predicates) :
    types = ready.header.bindings.map (fun binding => binding.1.scheme.body) ∧
      receipt.node.type = ready.header.function.resultType := by
  cases application with
  | intro member admissible declaration parameters result functionType predicates =>
    have shape := shaped _
      (signatures ▸ member) (by rw [← ready.metadata]; exact declaration)
    rw [← ready.metadata] at shape
    exact ⟨parameters.symm.trans shape.1, result.symm.trans shape.2⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationDirectSourceTypes
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationDirectArgumentRows
/-! Direct declaration calls retain the independently typed Source argument
row. Every raw replacement is closed; original Source admissibility recovers
its validity. Actual evidence production supplies the full callable dictionary;
authentic compiler bundles align native arguments only after the Source row
supplies physical arity. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationDirectArgumentRows
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Receipt)
open CallableIndexedOwnedPreparedStagedDirectCallAuthority (Port EvidenceAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {values : SourceCoreCompatibleValues.Context}
  {invocation : Staging.Recursive.Scope} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : Receipt policy body fuel compilation values invocation.source scope id callee ids
    instantiation reasonAt lowered)
  (port : Port receipt headers)
  {context : SourceSemantics.Context}
  (evidenceAt : EvidenceAt receipt port context invocation.evidence)

section Successful
variable {stages : Staging.Recursive.Registry} {environment : Dynamic.Environment}
  {before after : Dynamic.Heap} {sourceTypes : List TypeSystem.Ty}
  {arguments : List Dynamic.Value} {payloads : List Value}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {mapping : LocationMap} {world : StoreTyping}

include receipt port in
theorem at_successful_arguments
    (certified : SelectedCompilationNamedSourceTyping.Certified port.header)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
    (heapTyped : Dynamic.HeapWellTyped context after)
    (argumentsTyped : Dynamic.ValuesHaveTypes context after arguments
      (port.header.bindings.map (fun binding => binding.1.scheme.body)))
    (represented : DataExpressionSequence.Values model mapping world
      (port.header.bindings.map (fun binding => binding.1.scheme.body))
      (receipt.codes.map (·.type)) arguments payloads) :
    CallableIndexedParameterMeaning.Arguments model mapping world port.header.bindings arguments payloads ∧
      Dynamic.HeapWellTyped port.header.function.context after ∧
      Dynamic.ValuesHaveTypes port.header.function.context after arguments port.header.types ∧
      Dynamic.TypeContextSupports port.header.context context := by
  have binderCount : arguments.length = port.header.bindings.length := by
    simpa only [List.length_map] using
      (CallableIndexedOwnedStoredArgumentAlignment.source_length represented).symm
  have nativePacked : SourceCoreCompatibleCatalog.packTypes (receipt.codes.map (·.type)) =
      SourceCoreCompatibleCatalog.packTypes (port.header.bindings.map Prod.snd) :=
    (CompatibleExpressionConstructorNativeTyping.packed_type receipt.codes).symm.trans
      (receipt.parameter.symm.trans
        ((congrArg SourceCoreCalls.Signature.parameterType port.signature).symm.trans port.header.parameterType))
  have representedRows := CallableIndexedOwnedStoredArgumentAlignment.arguments_of_bundles
    port.header.bindings represented binderCount rfl nativePacked
  obtain ⟨bodyHeap, bodyArguments, supports⟩ :=
    SelectedCompilationNamedAdmission.arguments certified runtime heapTyped argumentsTyped
  exact ⟨representedRows, bodyHeap, bodyArguments, supports⟩
end Successful
end Solcore.SourceSemantics.CoreLowering.SelectedCompilationDirectArgumentRows
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationSharedCallerBounds
/-! One structural recursion supplies ordered child laws for every supported
expression. Genuine call receipts select internal head continuations, allowing
legacy and physical method callers to use their own reached state authority.
Source and native execution grades stay independent. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationSharedCallerBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (PacketFor SupportFor)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body)
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Certificate Calls DirectCalls MethodCalls)
open CallableIndexedOwnedPreparedStagedCallerHeadHandlers
open CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority (IndexReady)
universe u
open CallableLambdaBodyReachability

open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point CallsReady)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}

variable {readFuel : Nat}

section Generic

variable {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  {stages : Staging.Recursive.Registry}
  {semanticFaults : FunctionCalls.FaultRep}
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (unique : NodeOccurrencesUnique invocation.source)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (indexObservations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions
    (CallableIndexedLambdaValues.Identity compiled.indexed))
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry
    completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)

variable
  (sameLedger : context.solvedRequirements = compilation.solvedRequirements)
  (runtimeLedger : RuntimeRequirementLedgerValid context)
  (uninitialized : ∀ current child code,
    CompatibleExpressionReads.LoweredRead readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt current child code →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt child))
  {faultRoot : ExpressionId}
  (uninitializedOn : ∀ current child code,
    CompatibleExpressionReads.LoweredRead readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt current child code →
    Reaches invocation.source [.expression faultRoot] (.expression child) →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt child))

local notation "bridge" => callerBridge

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics

include callerBridge receiver functions runtime unique
  observations functionTypes indexObservations extension semantic sameLedger runtimeLedger uninitializedOn in
/-- Every strict Source child is supplied by structural recursion at its actual
reached state. The numeric family supplies only the chosen called-body laws below the fixed
budget; all caller child laws are constructed here. -/
theorem preserves_reached_with_functions
    (budget : Nat) {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
    {rootCode : SourceCoreBasic.LoweredExpr}
    (root : Certificate policy body compilation readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt rootScope rootId rootCode)
    (reached : Reaches invocation.source [.expression faultRoot] (.expression rootId)) :
    PreservesDirect bridge model stages callFaults budget root →
    PreservesMethod bridge model stages callFaults budget root → IndexReady root →
    PreservesIndirect bridge model stages callFaults budget root → ∀ size, size ≤ budget →
      PreservesAt bridge context model stages invocation
        (Point rootScope rootId rootCode) callFaults size := by
  revert reached
  induction root with
  | proxy receipt =>
      intro _reached _directHeads _methodHeads _indexReady _indirectHeads size _within current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedAdmittedStagedProxyBounds.preserves
        functions extension bridge unique callFaults size (.proxy receipt)
  | leaf tree =>
      intro reached _directHeads _methodHeads _indexReady _indirectHeads size _within current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact SelectedCompilationReadProductBounds.preserves_reached
        bridge functions extension sameLedger runtimeLedger callFaults uninitializedOn semantic
        unique size ⟨tree, reached⟩
  | @unary id node operand childNode operator operandType resultType core childCode metadata form found inputType outputType unaryProfile child ih =>
      intro reached directHeads methodHeads indexReady indirectHeads size within
      have reached0 : Reaches invocation.source [.expression faultRoot] (.expression operand) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have childMeaning : PreservesBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope [(operand, ⟨core.operandType, childCode⟩)]) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        have pair := Prod.mk.inj member
        obtain ⟨rfl, rfl⟩ := pair
        intro node
        exact ih reached0 (fun compiler inside => directHeads compiler (.unary_child
            (actual := metadata) (form := form) (found := found) (inputType := inputType) (outputType := outputType) (profile := unaryProfile) inside)) (fun compiler inside => methodHeads compiler (.unary_child
            (actual := metadata) (form := form) (found := found) (inputType := inputType) (outputType := outputType) (profile := unaryProfile) inside)) (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType (.unary_child
            (actual := metadata) (form := form) (found := found) (inputType := inputType) (outputType := outputType) (profile := unaryProfile) inside)) (fun compiler inside => indirectHeads compiler (.unary_child
            (actual := metadata) (form := form) (found := found) (inputType := inputType) (outputType := outputType) (profile := unaryProfile) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      apply SelectedCompilationOperatorBounds.preserves_at
        bridge functions size size (Nat.le_refl _) unique childMeaning
      exact .unary metadata form found inputType outputType unaryProfile (by exact ⟨rfl, by simp⟩)
  | @index id node base key baseNode keyNode layout comparison first second header keyFound form sourceType firstTree secondTree ihFirst ihSecond =>
      intro reached directHeads methodHeads indexReady indirectHeads size within
      have reached0 : Reaches invocation.source [.expression faultRoot] (.expression base) :=
        .expression reached header.metadata.found (by simp [form, ExpressionForm.references])
      have reached1 : Reaches invocation.source [.expression faultRoot] (.expression key) :=
        .expression reached header.metadata.found (by simp [form, ExpressionForm.references])
      have childMeaning : PreservesBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope [(base, first), (key, second)]) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with member0 | member1
        · have pair := Prod.mk.inj member0
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihFirst reached0
            (fun compiler inside => directHeads compiler (.index_base
              (header := header) (keyFound := keyFound) (form := form) (sourceType := sourceType)
              (firstTree := firstTree) (secondTree := secondTree) inside)) (fun compiler inside => methodHeads compiler (.index_base
              (header := header) (keyFound := keyFound) (form := form) (sourceType := sourceType)
              (firstTree := firstTree) (secondTree := secondTree) inside))
            (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType (.index_base
              (header := header) (keyFound := keyFound) (form := form) (sourceType := sourceType)
              (firstTree := firstTree) (secondTree := secondTree) inside))
            (fun compiler inside => indirectHeads compiler (.index_base
              (header := header) (keyFound := keyFound) (form := form) (sourceType := sourceType)
              (firstTree := firstTree) (secondTree := secondTree) inside))
            childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
        · have pair := Prod.mk.inj member1
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihSecond reached1
            (fun compiler inside => directHeads compiler (.index_key
              (header := header) (keyFound := keyFound) (form := form) (sourceType := sourceType)
              (firstTree := firstTree) (secondTree := secondTree) inside)) (fun compiler inside => methodHeads compiler (.index_key
              (header := header) (keyFound := keyFound) (form := form) (sourceType := sourceType)
              (firstTree := firstTree) (secondTree := secondTree) inside))
            (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType (.index_key
              (header := header) (keyFound := keyFound) (form := form) (sourceType := sourceType)
              (firstTree := firstTree) (secondTree := secondTree) inside))
            (fun compiler inside => indirectHeads compiler (.index_key
              (header := header) (keyFound := keyFound) (form := form) (sourceType := sourceType)
              (firstTree := firstTree) (secondTree := secondTree) inside))
            childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
      obtain ⟨port⟩ := indexReady header keyFound form sourceType (.here firstTree secondTree)
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact SelectedCompilationGeneralIndexBounds.preserves
        bridge functions callFaults unique header keyFound form sourceType
        (CallableIndexedLambdaValues.identity_faithful compiled.indexed) indexObservations functionTypes
        (children := RecursiveStageTupleMeaning.Entries current [(base, first), (key, second)])
        ⟨rfl, by simp⟩ ⟨rfl, by simp⟩ (port.missing receiver functions keyFound form)
        size childMeaning ⟨rfl, rfl, rfl⟩
  | @binary id node left right leftNode rightNode operator operandType resultType operatorMode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType binaryProfile first second ihFirst ihSecond =>
      intro reached directHeads methodHeads indexReady indirectHeads size within
      have reached0 : Reaches invocation.source [.expression faultRoot] (.expression left) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have reached1 : Reaches invocation.source [.expression faultRoot] (.expression right) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have childMeaning : PreservesBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope [(left, ⟨operatorMode.operandType operator, leftCode⟩), (right, ⟨operatorMode.operandType operator, rightCode⟩)]) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with member0 | member1
        · have pair := Prod.mk.inj member0
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihFirst reached0 (fun compiler inside => directHeads compiler (.binary_left
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun compiler inside => methodHeads compiler (.binary_left
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType (.binary_left
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun compiler inside => indirectHeads compiler (.binary_left
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
        · have pair := Prod.mk.inj member1
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihSecond reached1 (fun compiler inside => directHeads compiler (.binary_right
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun compiler inside => methodHeads compiler (.binary_right
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType (.binary_right
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun compiler inside => indirectHeads compiler (.binary_right
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      apply SelectedCompilationOperatorBounds.preserves_at
        bridge functions size size (Nat.le_refl _) unique childMeaning
      exact .binary metadata form leftFound rightFound leftType rightType outputType binaryProfile (by exact ⟨rfl, by simp⟩) (by exact ⟨rfl, by simp⟩)
  | @conditional id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree ihCondition ihThen ihElse =>
      intro reached directHeads methodHeads indexReady indirectHeads size within
      have reached0 : Reaches invocation.source [.expression faultRoot] (.expression condition) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have reached1 : Reaches invocation.source [.expression faultRoot] (.expression thenId) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have reached2 : Reaches invocation.source [.expression faultRoot] (.expression elseId) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have childMeaning : PreservesBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope [(condition, ⟨.bool, conditionCode⟩), (thenId, ⟨type, thenCode⟩), (elseId, ⟨type, elseCode⟩)]) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with member0 | member1 | member2
        · have pair := Prod.mk.inj member0
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihCondition reached0 (fun compiler inside => directHeads compiler (.conditional_condition
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => methodHeads compiler (.conditional_condition
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType (.conditional_condition
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => indirectHeads compiler (.conditional_condition
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
        · have pair := Prod.mk.inj member1
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihThen reached1 (fun compiler inside => directHeads compiler (.conditional_then
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => methodHeads compiler (.conditional_then
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType (.conditional_then
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => indirectHeads compiler (.conditional_then
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
        · have pair := Prod.mk.inj member2
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihElse reached2 (fun compiler inside => directHeads compiler (.conditional_else
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => methodHeads compiler (.conditional_else
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType (.conditional_else
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => indirectHeads compiler (.conditional_else
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      apply SelectedCompilationOperatorBounds.preserves_at
        bridge functions size size (Nat.le_refl _) unique childMeaning
      exact .conditional metadata form conditionFound thenFound elseFound conditionType thenType elseType (by exact ⟨rfl, by simp⟩) (by exact ⟨rfl, by simp⟩) (by exact ⟨rfl, by simp⟩)
  | @group id node inner innerNode code metadata form innerFound sourceType child ih =>
      intro reached directHeads methodHeads indexReady indirectHeads size within
      have innerReached : Reaches invocation.source [.expression faultRoot] (.expression inner) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have childMeaning : PreservesBelow bridge context model stages invocation
          (Point rootScope inner code) callFaults size := by
        intro childSize _smaller current child actual point
        obtain ⟨rfl, rfl, rfl⟩ := point
        exact ih innerReached (fun compiler inside => directHeads compiler
          (.group (actual := metadata) (form := form) (found := innerFound) (type := sourceType) inside)) (fun compiler inside => methodHeads compiler
          (.group (actual := metadata) (form := form) (found := innerFound) (type := sourceType) inside)) (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType
          (.group (actual := metadata) (form := form) (found := innerFound) (type := sourceType) inside)) (fun compiler inside => indirectHeads compiler
          (.group (actual := metadata) (form := form) (found := innerFound) (type := sourceType) inside)) childSize (Nat.le_trans (Nat.le_of_lt _smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child actual point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedGroupBounds.group_preserves bridge unique size
        childMeaning size (Nat.le_refl _) (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @tuple id node ids types codes header sequence children ih =>
      intro reached directHeads methodHeads indexReady indirectHeads size within
      have childReached : ∀ child code, (child, code) ∈ ids.zip codes →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        exact .expression reached header.metadata.found
          (by simp [header.form, ExpressionForm.references, (List.of_mem_zip member).1])
      have childMeaning : PreservesBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope (ids.zip codes)) callFaults size := by
        intro childSize _smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        exact ih child code member (childReached child code member)
          (fun compiler inside => directHeads compiler
          (.tuple_child (header := header) (sequence := sequence) (children := children) member inside)) (fun compiler inside => methodHeads compiler
          (.tuple_child (header := header) (sequence := sequence) (children := children) member inside)) (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType
          (.tuple_child (header := header) (sequence := sequence) (children := children) member inside)) (fun compiler inside => indirectHeads compiler
          (.tuple_child (header := header) (sequence := sequence) (children := children) member inside)) childSize (Nat.le_trans (Nat.le_of_lt _smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact SelectedCompilationTupleBounds.tuple_preserves
        bridge functions callFaults unique size childMeaning
        ⟨node, ids, types, codes, rfl, header, sequence⟩
  | @constructor id node instantiation ids tag headerWord codes header form admissible ranges count nodes sequence children ih =>
      intro reached directHeads methodHeads indexReady indirectHeads size within
      have childReached : ∀ child code, (child, code) ∈ ids.zip codes →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        exact .expression reached header.metadata.found
          (by simp [form, ExpressionForm.references, (List.of_mem_zip member).1])
      have childMeaning : PreservesBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope (ids.zip codes)) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        exact ih child code member (childReached child code member)
          (fun compiler inside => directHeads compiler
            (.constructor_child (header := header) (form := form) (admissible := admissible)
              (ranges := ranges) (count := count) (nodes := nodes)
              (sequence := sequence) (children := children) member inside)) (fun compiler inside => methodHeads compiler
            (.constructor_child (header := header) (form := form) (admissible := admissible)
              (ranges := ranges) (count := count) (nodes := nodes)
              (sequence := sequence) (children := children) member inside)) (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType
            (.constructor_child (header := header) (form := form) (admissible := admissible)
              (ranges := ranges) (count := count) (nodes := nodes)
              (sequence := sequence) (children := children) member inside)) (fun compiler inside => indirectHeads compiler
            (.constructor_child (header := header) (form := form) (admissible := admissible)
              (ranges := ranges) (count := count) (nodes := nodes)
              (sequence := sequence) (children := children) member inside))
          childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact SelectedCompilationConstructorBounds.constructor_preserves
        bridge functions extension callFaults unique runtime size childMeaning
        header form admissible ranges count nodes sequence ⟨rfl, rfl, rfl⟩
  | @builtin id callee ids function fuel lowered compiler calleeTyped sourceType nativeTypes sequence children ih =>
      intro reached directHeads methodHeads indexReady indirectHeads size within
      have childReached : ∀ child code, (child, code) ∈ ids.zip compiler.codes →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        exact .expression reached compiler.metadata.found
          (by simp [compiler.form, ExpressionForm.references, (List.of_mem_zip member).1])
      have childMeaning : PreservesBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope (ids.zip compiler.codes)) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        exact ih child code member (childReached child code member)
          (fun nested inside => directHeads nested
            (.builtin_child (outer := compiler) (calleeTyped := calleeTyped)
            (sourceType := sourceType) (nativeTypes := nativeTypes)
            (sequence := sequence) (children := children) member inside)) (fun nested inside => methodHeads nested
            (.builtin_child (outer := compiler) (calleeTyped := calleeTyped)
            (sourceType := sourceType) (nativeTypes := nativeTypes)
            (sequence := sequence) (children := children) member inside)) (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType
            (.builtin_child (outer := compiler) (calleeTyped := calleeTyped)
            (sourceType := sourceType) (nativeTypes := nativeTypes)
            (sequence := sequence) (children := children) member inside)) (fun nested inside => indirectHeads nested
            (.builtin_child (outer := compiler) (calleeTyped := calleeTyped)
            (sourceType := sourceType) (nativeTypes := nativeTypes)
            (sequence := sequence) (children := children) member inside))
          childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact SelectedCompilationDirectBuiltinBounds.preserves
        bridge functions observations callFaults unique
        (compiler.result ▸ compiler.metadata) compiler.form nativeTypes size sequence childMeaning
        ⟨rfl, rfl, compiler.output⟩
  | @direct id callee ids instantiation fuel lowered types compiler calleeTyped application sequence children ih =>
      intro reached directHeads methodHeads indexReady indirectHeads size within
      have childReached : ∀ child code, (child, code) ∈ ids.zip compiler.codes →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        apply Reaches.expression reached compiler.metadata.found
        simp [compiler.form, ExpressionForm.references, (List.of_mem_zip member).1]
      have childMeaning : PreservesBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope (ids.zip compiler.codes)) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        exact ih child code member (childReached child code member)
          (fun nested inside => directHeads nested
            (.direct_child (outer := compiler) (calleeTyped := calleeTyped) (application := application)
              (sequence := sequence) (children := children) member inside)) (fun nested inside => methodHeads nested
            (.direct_child (outer := compiler) (calleeTyped := calleeTyped) (application := application)
              (sequence := sequence) (children := children) member inside)) (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType
            (.direct_child (outer := compiler) (calleeTyped := calleeTyped) (application := application)
              (sequence := sequence) (children := children) member inside))
          (fun nested inside => indirectHeads nested
            (.direct_child (outer := compiler) (calleeTyped := calleeTyped) (application := application)
              (sequence := sequence) (children := children) member inside))
          childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      exact directHeads compiler (.here calleeTyped application sequence children)
        calleeTyped application sequence size within childMeaning point
  | @method id fuel lowered types compiler sequence children ih =>
      intro reached directHeads methodHeads indexReady indirectHeads size within
      have childReached : ∀ child code, (child, code) ∈ compiler.arguments.zip compiler.codes →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        exact .expression reached compiler.metadata.found
          (compiler.argument_references (List.of_mem_zip member).1)
      have childMeaning : PreservesBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope (compiler.arguments.zip compiler.codes)) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        exact ih child code member (childReached child code member)
          (fun nested inside => directHeads nested (.method_child (outer := compiler)
            (sequence := sequence) (children := children) member inside))
          (fun nested inside => methodHeads nested (.method_child (outer := compiler)
            (sequence := sequence) (children := children) member inside))
          (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType
            (.method_child (outer := compiler) (sequence := sequence) (children := children) member inside))
          (fun nested inside => indirectHeads nested (.method_child (outer := compiler)
            (sequence := sequence) (children := children) member inside))
          childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      exact methodHeads compiler (.here sequence children) sequence size within childMeaning point
  | @call id callee ids metadata fuel lowered types compiler sequence children ih =>
      intro reached directHeads methodHeads indexReady indirectHeads size within
      have childReached : ∀ child code, (child, code) ∈ compiler.entries →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        apply Reaches.expression reached compiler.found
        simp only [CallableIndirectCallCertificates.Receipt.entries, List.mem_cons] at member
        rcases member with same | member
        · have sameId : child = callee := congrArg Prod.fst same
          simp [compiler.originalForm, ExpressionForm.references, sameId]
        · simp [compiler.originalForm, ExpressionForm.references, (List.of_mem_zip member).1]
      have childMeaning : PreservesBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope compiler.entries) callFaults size := by
        intro childSize _smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        exact ih child code member (childReached child code member)
          (fun nested inside => directHeads nested
          (.call_child (outer := compiler) (sequence := sequence) (children := children) member inside)) (fun nested inside => methodHeads nested
          (.call_child (outer := compiler) (sequence := sequence) (children := children) member inside)) (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType
          (.call_child (outer := compiler) (sequence := sequence) (children := children) member inside)) (fun nested inside => indirectHeads nested
          (.call_child (outer := compiler) (sequence := sequence) (children := children) member inside)) childSize (Nat.le_trans (Nat.le_of_lt _smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      exact indirectHeads compiler (.here sequence children) sequence size within childMeaning point

include callerBridge receiver functions runtime unique
  observations functionTypes indexObservations extension semantic sameLedger runtimeLedger uninitializedOn in
/-- Every child native grade comes from structural recursion. The returned
Source grade is independent, including exact nested stage failure scope. -/
theorem reflects_reached_with_functions
    (budget : Nat)
    {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
    {rootCode : SourceCoreBasic.LoweredExpr}
    (root : Certificate policy body compilation readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt rootScope rootId rootCode)
    (reached : Reaches invocation.source [.expression faultRoot] (.expression rootId)) :
    ReflectsDirect bridge model stages callFaults budget root →
    ReflectsMethod bridge model stages callFaults budget root → IndexReady root →
    ReflectsIndirect bridge model stages callFaults budget root → ∀ size, size ≤ budget →
      ReflectsAt bridge context model stages invocation
        (Point rootScope rootId rootCode) callFaults size := by
  revert reached
  induction root with
  | proxy receipt =>
      intro _reached _directHeads _methodHeads _indexReady _indirectHeads size _within current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedAdmittedStagedProxyBounds.reflects
        functions extension bridge callFaults size (.proxy receipt)
  | leaf tree =>
      intro reached _directHeads _methodHeads _indexReady _indirectHeads size _within current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact SelectedCompilationReadProductBounds.reflects_reached
        bridge functions extension sameLedger runtimeLedger callFaults uninitializedOn semantic
        unique size ⟨tree, reached⟩
  | @unary id node operand childNode operator operandType resultType core childCode metadata form found inputType outputType unaryProfile child ih =>
      intro reached directHeads methodHeads indexReady indirectHeads size within
      have reached0 : Reaches invocation.source [.expression faultRoot] (.expression operand) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have childMeaning : ReflectsBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope [(operand, ⟨core.operandType, childCode⟩)]) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        have pair := Prod.mk.inj member
        obtain ⟨rfl, rfl⟩ := pair
        intro node
        exact ih reached0 (fun compiler inside => directHeads compiler (.unary_child
            (actual := metadata) (form := form) (found := found) (inputType := inputType) (outputType := outputType) (profile := unaryProfile) inside)) (fun compiler inside => methodHeads compiler (.unary_child
            (actual := metadata) (form := form) (found := found) (inputType := inputType) (outputType := outputType) (profile := unaryProfile) inside)) (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType (.unary_child
            (actual := metadata) (form := form) (found := found) (inputType := inputType) (outputType := outputType) (profile := unaryProfile) inside)) (fun compiler inside => indirectHeads compiler (.unary_child
            (actual := metadata) (form := form) (found := found) (inputType := inputType) (outputType := outputType) (profile := unaryProfile) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      apply SelectedCompilationOperatorBounds.reflects_at
        bridge functions size size (Nat.le_refl _) unique childMeaning
      exact .unary metadata form found inputType outputType unaryProfile (by exact ⟨rfl, by simp⟩)
  | @index id node base key baseNode keyNode layout comparison first second header keyFound form sourceType firstTree secondTree ihFirst ihSecond =>
      intro reached directHeads methodHeads indexReady indirectHeads size within
      have reached0 : Reaches invocation.source [.expression faultRoot] (.expression base) :=
        .expression reached header.metadata.found (by simp [form, ExpressionForm.references])
      have reached1 : Reaches invocation.source [.expression faultRoot] (.expression key) :=
        .expression reached header.metadata.found (by simp [form, ExpressionForm.references])
      have childMeaning : ReflectsBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope [(base, first), (key, second)]) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with member0 | member1
        · have pair := Prod.mk.inj member0
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihFirst reached0
            (fun compiler inside => directHeads compiler (.index_base
              (header := header) (keyFound := keyFound) (form := form) (sourceType := sourceType)
              (firstTree := firstTree) (secondTree := secondTree) inside)) (fun compiler inside => methodHeads compiler (.index_base
              (header := header) (keyFound := keyFound) (form := form) (sourceType := sourceType)
              (firstTree := firstTree) (secondTree := secondTree) inside))
            (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType (.index_base
              (header := header) (keyFound := keyFound) (form := form) (sourceType := sourceType)
              (firstTree := firstTree) (secondTree := secondTree) inside))
            (fun compiler inside => indirectHeads compiler (.index_base
              (header := header) (keyFound := keyFound) (form := form) (sourceType := sourceType)
              (firstTree := firstTree) (secondTree := secondTree) inside))
            childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
        · have pair := Prod.mk.inj member1
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihSecond reached1
            (fun compiler inside => directHeads compiler (.index_key
              (header := header) (keyFound := keyFound) (form := form) (sourceType := sourceType)
              (firstTree := firstTree) (secondTree := secondTree) inside)) (fun compiler inside => methodHeads compiler (.index_key
              (header := header) (keyFound := keyFound) (form := form) (sourceType := sourceType)
              (firstTree := firstTree) (secondTree := secondTree) inside))
            (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType (.index_key
              (header := header) (keyFound := keyFound) (form := form) (sourceType := sourceType)
              (firstTree := firstTree) (secondTree := secondTree) inside))
            (fun compiler inside => indirectHeads compiler (.index_key
              (header := header) (keyFound := keyFound) (form := form) (sourceType := sourceType)
              (firstTree := firstTree) (secondTree := secondTree) inside))
            childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
      obtain ⟨port⟩ := indexReady header keyFound form sourceType (.here firstTree secondTree)
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact SelectedCompilationGeneralIndexBounds.reflects
        bridge functions callFaults unique header keyFound form sourceType
        (CallableIndexedLambdaValues.identity_faithful compiled.indexed) indexObservations functionTypes
        (children := RecursiveStageTupleMeaning.Entries current [(base, first), (key, second)])
        ⟨rfl, by simp⟩ ⟨rfl, by simp⟩ (port.missing receiver functions keyFound form)
        size childMeaning ⟨rfl, rfl, rfl⟩
  | @binary id node left right leftNode rightNode operator operandType resultType operatorMode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType binaryProfile first second ihFirst ihSecond =>
      intro reached directHeads methodHeads indexReady indirectHeads size within
      have reached0 : Reaches invocation.source [.expression faultRoot] (.expression left) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have reached1 : Reaches invocation.source [.expression faultRoot] (.expression right) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have childMeaning : ReflectsBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope [(left, ⟨operatorMode.operandType operator, leftCode⟩), (right, ⟨operatorMode.operandType operator, rightCode⟩)]) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with member0 | member1
        · have pair := Prod.mk.inj member0
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihFirst reached0 (fun compiler inside => directHeads compiler (.binary_left
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun compiler inside => methodHeads compiler (.binary_left
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType (.binary_left
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun compiler inside => indirectHeads compiler (.binary_left
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
        · have pair := Prod.mk.inj member1
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihSecond reached1 (fun compiler inside => directHeads compiler (.binary_right
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun compiler inside => methodHeads compiler (.binary_right
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType (.binary_right
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun compiler inside => indirectHeads compiler (.binary_right
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      apply SelectedCompilationOperatorBounds.reflects_at
        bridge functions size size (Nat.le_refl _) unique childMeaning
      exact .binary metadata form leftFound rightFound leftType rightType outputType binaryProfile (by exact ⟨rfl, by simp⟩) (by exact ⟨rfl, by simp⟩)
  | @conditional id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree ihCondition ihThen ihElse =>
      intro reached directHeads methodHeads indexReady indirectHeads size within
      have reached0 : Reaches invocation.source [.expression faultRoot] (.expression condition) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have reached1 : Reaches invocation.source [.expression faultRoot] (.expression thenId) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have reached2 : Reaches invocation.source [.expression faultRoot] (.expression elseId) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have childMeaning : ReflectsBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope [(condition, ⟨.bool, conditionCode⟩), (thenId, ⟨type, thenCode⟩), (elseId, ⟨type, elseCode⟩)]) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with member0 | member1 | member2
        · have pair := Prod.mk.inj member0
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihCondition reached0 (fun compiler inside => directHeads compiler (.conditional_condition
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => methodHeads compiler (.conditional_condition
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType (.conditional_condition
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => indirectHeads compiler (.conditional_condition
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
        · have pair := Prod.mk.inj member1
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihThen reached1 (fun compiler inside => directHeads compiler (.conditional_then
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => methodHeads compiler (.conditional_then
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType (.conditional_then
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => indirectHeads compiler (.conditional_then
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
        · have pair := Prod.mk.inj member2
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihElse reached2 (fun compiler inside => directHeads compiler (.conditional_else
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => methodHeads compiler (.conditional_else
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType (.conditional_else
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => indirectHeads compiler (.conditional_else
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      apply SelectedCompilationOperatorBounds.reflects_at
        bridge functions size size (Nat.le_refl _) unique childMeaning
      exact .conditional metadata form conditionFound thenFound elseFound conditionType thenType elseType (by exact ⟨rfl, by simp⟩) (by exact ⟨rfl, by simp⟩) (by exact ⟨rfl, by simp⟩)
  | @group id node inner innerNode code metadata form innerFound sourceType child ih =>
      intro reached directHeads methodHeads indexReady indirectHeads size within
      have innerReached : Reaches invocation.source [.expression faultRoot] (.expression inner) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have childMeaning : ReflectsAt bridge context model stages invocation
          (Point rootScope inner code) callFaults size := by
        intro current child actual point
        obtain ⟨rfl, rfl, rfl⟩ := point
        exact ih innerReached (fun compiler inside => directHeads compiler
          (.group (actual := metadata) (form := form) (found := innerFound) (type := sourceType) inside)) (fun compiler inside => methodHeads compiler
          (.group (actual := metadata) (form := form) (found := innerFound) (type := sourceType) inside)) (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType
          (.group (actual := metadata) (form := form) (found := innerFound) (type := sourceType) inside)) (fun compiler inside => indirectHeads compiler
          (.group (actual := metadata) (form := form) (found := innerFound) (type := sourceType) inside)) size within ⟨rfl, rfl, rfl⟩
      intro current child actual point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedGroupBounds.group_reflects bridge unique size
        childMeaning (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @tuple id node ids types codes header sequence children ih =>
      intro reached directHeads methodHeads indexReady indirectHeads size within
      have childReached : ∀ child code, (child, code) ∈ ids.zip codes →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        exact .expression reached header.metadata.found
          (by simp [header.form, ExpressionForm.references, (List.of_mem_zip member).1])
      have childMeaning : ReflectsBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope (ids.zip codes)) callFaults (size + 1) := by
        intro childSize _smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        exact ih child code member (childReached child code member)
          (fun compiler inside => directHeads compiler
          (.tuple_child (header := header) (sequence := sequence) (children := children) member inside)) (fun compiler inside => methodHeads compiler
          (.tuple_child (header := header) (sequence := sequence) (children := children) member inside)) (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType
          (.tuple_child (header := header) (sequence := sequence) (children := children) member inside)) (fun compiler inside => indirectHeads compiler
          (.tuple_child (header := header) (sequence := sequence) (children := children) member inside)) childSize (Nat.le_trans (Nat.le_of_lt_succ _smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact SelectedCompilationTupleBounds.tuple_reflects
        bridge functions callFaults unique size childMeaning
        ⟨node, ids, types, codes, rfl, header, sequence⟩
  | @constructor id node instantiation ids tag headerWord codes header form admissible ranges count nodes sequence children ih =>
      intro reached directHeads methodHeads indexReady indirectHeads size within
      have childReached : ∀ child code, (child, code) ∈ ids.zip codes →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        exact .expression reached header.metadata.found
          (by simp [form, ExpressionForm.references, (List.of_mem_zip member).1])
      have childMeaning : ReflectsBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope (ids.zip codes)) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        exact ih child code member (childReached child code member)
          (fun compiler inside => directHeads compiler
            (.constructor_child (header := header) (form := form) (admissible := admissible)
              (ranges := ranges) (count := count) (nodes := nodes)
              (sequence := sequence) (children := children) member inside)) (fun compiler inside => methodHeads compiler
            (.constructor_child (header := header) (form := form) (admissible := admissible)
              (ranges := ranges) (count := count) (nodes := nodes)
              (sequence := sequence) (children := children) member inside)) (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType
            (.constructor_child (header := header) (form := form) (admissible := admissible)
              (ranges := ranges) (count := count) (nodes := nodes)
              (sequence := sequence) (children := children) member inside)) (fun compiler inside => indirectHeads compiler
            (.constructor_child (header := header) (form := form) (admissible := admissible)
              (ranges := ranges) (count := count) (nodes := nodes)
              (sequence := sequence) (children := children) member inside))
          childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact SelectedCompilationConstructorBounds.constructor_reflects
        bridge functions extension callFaults unique runtime size childMeaning
        header form admissible ranges count nodes sequence ⟨rfl, rfl, rfl⟩
  | @builtin id callee ids function fuel lowered compiler calleeTyped sourceType nativeTypes sequence children ih =>
      intro reached directHeads methodHeads indexReady indirectHeads size within
      have childReached : ∀ child code, (child, code) ∈ ids.zip compiler.codes →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        exact .expression reached compiler.metadata.found
          (by simp [compiler.form, ExpressionForm.references, (List.of_mem_zip member).1])
      have childMeaning : ReflectsBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope (ids.zip compiler.codes)) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        exact ih child code member (childReached child code member)
          (fun nested inside => directHeads nested
            (.builtin_child (outer := compiler) (calleeTyped := calleeTyped)
            (sourceType := sourceType) (nativeTypes := nativeTypes)
            (sequence := sequence) (children := children) member inside)) (fun nested inside => methodHeads nested
            (.builtin_child (outer := compiler) (calleeTyped := calleeTyped)
            (sourceType := sourceType) (nativeTypes := nativeTypes)
            (sequence := sequence) (children := children) member inside)) (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType
            (.builtin_child (outer := compiler) (calleeTyped := calleeTyped)
            (sourceType := sourceType) (nativeTypes := nativeTypes)
            (sequence := sequence) (children := children) member inside)) (fun nested inside => indirectHeads nested
            (.builtin_child (outer := compiler) (calleeTyped := calleeTyped)
            (sourceType := sourceType) (nativeTypes := nativeTypes)
            (sequence := sequence) (children := children) member inside))
          childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact SelectedCompilationDirectBuiltinBounds.reflects
        bridge functions observations callFaults unique
        (compiler.result ▸ compiler.metadata) compiler.form nativeTypes size sequence childMeaning
        ⟨rfl, rfl, compiler.output⟩
  | @direct id callee ids instantiation fuel lowered types compiler calleeTyped application sequence children ih =>
      intro reached directHeads methodHeads indexReady indirectHeads size within
      have childReached : ∀ child code, (child, code) ∈ ids.zip compiler.codes →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        apply Reaches.expression reached compiler.metadata.found
        simp [compiler.form, ExpressionForm.references, (List.of_mem_zip member).1]
      have childMeaning : ReflectsBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope (ids.zip compiler.codes)) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        exact ih child code member (childReached child code member)
          (fun nested inside => directHeads nested
            (.direct_child (outer := compiler) (calleeTyped := calleeTyped) (application := application)
              (sequence := sequence) (children := children) member inside)) (fun nested inside => methodHeads nested
            (.direct_child (outer := compiler) (calleeTyped := calleeTyped) (application := application)
              (sequence := sequence) (children := children) member inside)) (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType
            (.direct_child (outer := compiler) (calleeTyped := calleeTyped) (application := application)
              (sequence := sequence) (children := children) member inside))
          (fun nested inside => indirectHeads nested
            (.direct_child (outer := compiler) (calleeTyped := calleeTyped) (application := application)
              (sequence := sequence) (children := children) member inside))
          childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      exact directHeads compiler (.here calleeTyped application sequence children)
        calleeTyped application sequence size within childMeaning point
  | @method id fuel lowered types compiler sequence children ih =>
      intro reached directHeads methodHeads indexReady indirectHeads size within
      have childReached : ∀ child code, (child, code) ∈ compiler.arguments.zip compiler.codes →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        exact .expression reached compiler.metadata.found
          (compiler.argument_references (List.of_mem_zip member).1)
      have childMeaning : ReflectsBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope (compiler.arguments.zip compiler.codes)) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        exact ih child code member (childReached child code member)
          (fun nested inside => directHeads nested (.method_child (outer := compiler)
            (sequence := sequence) (children := children) member inside))
          (fun nested inside => methodHeads nested (.method_child (outer := compiler)
            (sequence := sequence) (children := children) member inside))
          (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType
            (.method_child (outer := compiler) (sequence := sequence) (children := children) member inside))
          (fun nested inside => indirectHeads nested (.method_child (outer := compiler)
            (sequence := sequence) (children := children) member inside))
          childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      exact methodHeads compiler (.here sequence children) sequence size within childMeaning point
  | @call id callee ids metadata fuel lowered types compiler sequence children ih =>
      intro reached directHeads methodHeads indexReady indirectHeads size within
      have childReached : ∀ child code, (child, code) ∈ compiler.entries →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        apply Reaches.expression reached compiler.found
        simp only [CallableIndirectCallCertificates.Receipt.entries, List.mem_cons] at member
        rcases member with same | member
        · have sameId : child = callee := congrArg Prod.fst same
          simp [compiler.originalForm, ExpressionForm.references, sameId]
        · simp [compiler.originalForm, ExpressionForm.references, (List.of_mem_zip member).1]
      have childMeaning : ReflectsBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope compiler.entries) callFaults size := by
        intro childSize _smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        exact ih child code member (childReached child code member)
          (fun nested inside => directHeads nested
          (.call_child (outer := compiler) (sequence := sequence) (children := children) member inside)) (fun nested inside => methodHeads nested
          (.call_child (outer := compiler) (sequence := sequence) (children := children) member inside)) (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType
          (.call_child (outer := compiler) (sequence := sequence) (children := children) member inside)) (fun nested inside => indirectHeads nested
          (.call_child (outer := compiler) (sequence := sequence) (children := children) member inside)) childSize (Nat.le_trans (Nat.le_of_lt _smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      exact indirectHeads compiler (.here sequence children) sequence size within childMeaning point

end Generic

section Compatibility

variable {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers)
      owner compilation.administrativePrefix index.scope index.canonical) callerProtocol)
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  {stages : Staging.Recursive.Registry}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (unique : NodeOccurrencesUnique invocation.source)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry
    completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (closurePackets : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore), PacketFor association stages)
  (closureSupport : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore), SupportFor association stages (closurePackets association))
  (namedTerminals : ∀ header, header ∈ headers → Body header)

variable
  (sameLedger : context.solvedRequirements = compilation.solvedRequirements)
  (runtimeLedger : RuntimeRequirementLedgerValid context)
  (uninitialized : ∀ current child code,
    CompatibleExpressionReads.LoweredRead readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt current child code →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt child))
  {faultRoot : ExpressionId}
  (uninitializedOn : ∀ current child code,
    CompatibleExpressionReads.LoweredRead readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt current child code →
    Reaches invocation.source [.expression faultRoot] (.expression child) →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt child))

local notation "bridge" => callerBridge.forgetSlots

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics


include callerBridge receiver profile runtime unique
  observations extension semantic sameLedger runtimeLedger uninitializedOn in
theorem preserves_reached
    (budget : Nat) {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
    {rootCode : SourceCoreBasic.LoweredExpr}
    (root : Certificate policy body compilation readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt rootScope rootId rootCode)
    (reached : Reaches invocation.source [.expression faultRoot] (.expression rootId)) :
    PreservesDirect bridge model stages callFaults budget root →
    PreservesMethod bridge model stages callFaults budget root → IndexReady root →
    PreservesIndirect bridge model stages callFaults budget root → ∀ size, size ≤ budget →
      PreservesAt bridge context model stages invocation
        (Point rootScope rootId rootCode) callFaults size := by
  exact preserves_reached_with_functions callerBridge.forgetSlots receiver functions runtime unique
    observations (CallableIndexedOwnedContextualFunctionViews.runtime_views profile)
    (CallableIndexedOwnedContextualFunctionViews.observations profile) extension semantic sameLedger runtimeLedger uninitializedOn budget root reached

include callerBridge receiver profile runtime unique
  observations extension semantic sameLedger runtimeLedger uninitializedOn in
theorem reflects_reached
    (budget : Nat)
    {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
    {rootCode : SourceCoreBasic.LoweredExpr}
    (root : Certificate policy body compilation readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt rootScope rootId rootCode)
    (reached : Reaches invocation.source [.expression faultRoot] (.expression rootId)) :
    ReflectsDirect bridge model stages callFaults budget root →
    ReflectsMethod bridge model stages callFaults budget root → IndexReady root →
    ReflectsIndirect bridge model stages callFaults budget root → ∀ size, size ≤ budget →
      ReflectsAt bridge context model stages invocation
        (Point rootScope rootId rootCode) callFaults size := by
  exact reflects_reached_with_functions callerBridge.forgetSlots receiver functions runtime unique
    observations (CallableIndexedOwnedContextualFunctionViews.runtime_views profile)
    (CallableIndexedOwnedContextualFunctionViews.observations profile) extension semantic sameLedger runtimeLedger uninitializedOn budget root reached

end Compatibility

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationSharedCallerBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationRawDirectSourceTypes
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationRawDirectSourceTypes
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedRawDirectAuthority (Ready)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {project : SourceCoreEvidence.Projector} {caller : SourceSpecialization.SpecializedFunction}
  {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child} {budget : Nat}
  {source : TypedSource} {scope : SourceCoreBasic.Scope} {id callee : ExpressionId}
  {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
  {reasonAt : ExpressionId → Word} {callables : SourceCoreFunctions.CallablePolicy}
  {node : ExpressionNode} {output : SourceCoreBasic.LoweredExpr}
  (actual : CallableCoercionExpressionCertificates.Direct compiled.sourceProgram project caller compilation
    child budget source scope id callee ids instantiation reasonAt callables node output)

theorem source_types
    {catalog : List (CallableIndexedOwnedFunctionValues.Header compiled
      (Program.ofChecked compiled.sourceProgram))}
    (ready : Ready actual catalog) {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    (shaped : SelectedCompilationSourceSignatureFacts.Shape ready.header)
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (application : DeclarationApplicationValid context instantiation types node.rawType instantiation.predicates) :
    types = ready.header.bindings.map (fun binding => binding.1.scheme.body) ∧
      node.rawType = ready.header.function.resultType := by
  cases application with
  | intro member admissible declaration parameters result functionType predicates =>
    have shape := shaped _
      (signatures ▸ member) (by rw [← ready.metadata]; exact declaration)
    rw [← ready.metadata] at shape
    exact ⟨parameters.symm.trans shape.1, result.symm.trans shape.2⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationRawDirectSourceTypes
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationRawDirectArgumentRows
/-! Direct declaration calls retain the independently typed Source argument
row. Every raw replacement is closed; original Source admissibility recovers
its validity. Actual evidence production supplies the full callable dictionary;
authentic compiler bundles align native arguments only after the Source row
supplies physical arity. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationRawDirectArgumentRows
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedStagedRawDirectAuthority (Port EvidenceAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {project : SourceCoreEvidence.Projector} {caller : SourceSpecialization.SpecializedFunction}
  {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child} {fuel : Nat}
  {invocation : Staging.Recursive.Scope} {scope : SourceCoreBasic.Scope} {id callee : ExpressionId}
  {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
  {reasonAt : ExpressionId → Word} {callables : SourceCoreFunctions.CallablePolicy}
  {node : ExpressionNode} {output : SourceCoreBasic.LoweredExpr}
  (receipt : CallableCoercionExpressionCertificates.Direct compiled.sourceProgram project caller compilation
    child fuel invocation.source scope id callee ids instantiation reasonAt callables node output)
  (port : Port receipt headers)
  {context : SourceSemantics.Context}
  (evidenceAt : EvidenceAt receipt port context invocation.evidence)

section Successful
variable {stages : Staging.Recursive.Registry} {environment : Dynamic.Environment}
  {before after : Dynamic.Heap} {sourceTypes : List TypeSystem.Ty}
  {arguments : List Dynamic.Value} {payloads : List Value}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {mapping : LocationMap} {world : StoreTyping}

include receipt port in
theorem at_successful_arguments
    (certified : SelectedCompilationNamedSourceTyping.Certified port.header)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
    (heapTyped : Dynamic.HeapWellTyped context after)
    (argumentsTyped : Dynamic.ValuesHaveTypes context after arguments
      (port.header.bindings.map (fun binding => binding.1.scheme.body)))
    (represented : DataExpressionSequence.Values model mapping world
      (port.header.bindings.map (fun binding => binding.1.scheme.body))
      (receipt.loweredArguments.map (·.type)) arguments payloads) :
    CallableIndexedParameterMeaning.Arguments model mapping world port.header.bindings arguments payloads ∧
      Dynamic.HeapWellTyped port.header.function.context after ∧
      Dynamic.ValuesHaveTypes port.header.function.context after arguments port.header.types ∧
      Dynamic.TypeContextSupports port.header.context context := by
  have binderCount : arguments.length = port.header.bindings.length := by
    simpa only [List.length_map] using
      (CallableIndexedOwnedStoredArgumentAlignment.source_length represented).symm
  have nativePacked : SourceCoreCompatibleCatalog.packTypes (receipt.loweredArguments.map (·.type)) =
      SourceCoreCompatibleCatalog.packTypes (port.header.bindings.map Prod.snd) :=
    (CompatibleExpressionConstructorNativeTyping.packed_type receipt.loweredArguments).symm.trans
      (receipt.native.inputType.symm.trans
        ((congrArg SourceCoreCalls.Signature.parameterType port.signature).symm.trans port.header.parameterType))
  have representedRows := CallableIndexedOwnedStoredArgumentAlignment.arguments_of_bundles
    port.header.bindings represented binderCount rfl nativePacked
  obtain ⟨bodyHeap, bodyArguments, supports⟩ :=
    SelectedCompilationNamedAdmission.arguments certified runtime heapTyped argumentsTyped
  exact ⟨representedRows, bodyHeap, bodyArguments, supports⟩
end Successful
end Solcore.SourceSemantics.CoreLowering.SelectedCompilationRawDirectArgumentRows
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationDirectBounds
/-! A direct call uses its actual compiler-selected global slot after the
ordered arguments have run. That slot comes from the caller's canonical
receipt; the reached pool supplies its current capture. The same named-body
ports retain independent Source and native grades and restore the caller. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationDirectBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof DataPatternValues
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Receipt)
open CallableIndexedOwnedPreparedStagedDirectCallAuthority (Port EvidenceAt)
universe u

open CallableIndexedOwnedPreparedStagedDirectHeadBounds (Point)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : Receipt policy body fuel compilation (.initial compiled.compatible.checked)
    invocation.source scope id callee ids instantiation reasonAt lowered)
  (port : Port receipt headers)
  (evidenceAt : EvidenceAt receipt port context invocation.evidence)
  (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers)
      owner compilation.administrativePrefix index.scope index.canonical) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  (faults : RecursiveStageMeaning.FaultRep)
  (unique : NodeOccurrencesUnique invocation.source)
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (certified : SelectedCompilationNamedSourceTyping.Certified port.header)
  (shaped : SelectedCompilationSourceSignatureFacts.Shape port.header)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)

local notation "bridge" => callerBridge.forgetSlots
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

private theorem result_type : lowered.type = port.header.output :=
  receipt.result.symm.trans ((congrArg SourceCoreCalls.Signature.resultType port.signature).symm.trans port.header.resultType)

private theorem parameter_type : port.header.named.signature.parameterType =
    (SourceCoreCalls.packArguments receipt.codes).type := by
  rw [port.signature]
  exact receipt.parameter

section Preservation
variable {stages : Staging.Recursive.Registry}

include owner receipt port evidenceAt callerBridge functions faults unique owners certified shaped runtime in
theorem preserves {children : GenericExpressionMeaning.Certificate}
    (size : Nat)
    (sequence : DataExpressionSequence.Tree invocation.source children scope ids
      (port.header.bindings.map (fun binding => binding.1.scheme.body)) receipt.codes)
    (childMeaning : PreservesBelow bridge context model stages invocation children faults size)
    (bodyMeaning : ∀ {child : Staging.Recursive.Scope}, stages.Closure port.header.function child →
      CallableIndexedOwnedPreparedStagedNamedBodyPorts.PreservesBelow (headers := headers) (keys := keys)
        port.header model stages child faults size) :
    PreservesAt bridge context model stages invocation (Point scope id lowered) faults size := by
  intro current child code point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted trace
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans receipt.metadata.found)
  obtain ⟨sourceTypes, calleeValid, application, typing⟩ :=
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.source_types unique receipt.metadata.found
      receipt.form receipt.metadata.coercions typed
  have rows := SelectedCompilationDirectSourceTypes.source_types receipt port.toReady shaped runtime.signatures application
  have orderedTyping := rows.1 ▸ typing
  have nativeResult := result_type receipt port
  have parameter := parameter_type receipt port
  rcases CallableIndexedOwnedPreparedStagedDirectSourceInversion.children
      unique receipt.metadata.found receipt.form receipt.metadata.coercions trace with
    ⟨sequenceSize, invocationSize, argumentsHeap, sources, name, evidence, sameSize,
      calleeOccurrence, valid, sourceTrace, produced, invoked⟩ |
    ⟨sequenceSize, failure, sameSize, outcomeEq, sourceTrace⟩
  · have argumentsWithin : sequenceSize ≤ size := Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))
    have invocationWithin : invocationSize ≤ size := Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))
    obtain ⟨values, middleStore, middleMap, middleWorld, argumentsEvaluated, represented, middleHeaps,
        argumentMaps, argumentWorlds, argumentFrame, argumentMetadata, reached, related, post⟩ :=
      SelectedCompilationExpressionSequence.preserves_values bridge size sequence unique orderedTyping
        childMeaning environments heaps locals agrees actualTyped initial admitted sourceTrace argumentsWithin
    obtain ⟨parameters, headerHeap, headerArguments, supports⟩ :=
      SelectedCompilationDirectArgumentRows.at_successful_arguments receipt port
        certified runtime post.at_values.heap post.values_typed represented
    have sourceEq := CallableIndexedOwnedPreparedStagedDirectArgumentRows.global_eq receipt port evidenceAt produced
    rw [sourceEq] at invoked
    obtain ⟨capture⟩ := CallableIndexedOwnedFunctionEntries.capture_from_pool
      (callerBridge.pool reached) owner port.member
    let nativeCapture := CallableIndexedOwnedFunctionValues.NamedCapture.of_capture capture
    obtain ⟨value, finalStore, finalMap, finalWorld, bodyEvaluated, result, finalHeaps,
        bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, finalState, bodyRelated, bodyPost⟩ :=
      SelectedCompilationNamedInvocationPreservation.preserves_invocation
        functions owner (callerBridge.pool reached) port.header nativeCapture port.sourceAt
        port.aligned.layouts port.member owners certified post.at_values.rows headerHeap headerArguments
        parameters middleHeaps supports size bodyMeaning invoked invocationWithin
    have selected := OptionalCell.read_success compilation.internalReason
      (show Evaluates (packValues values :: actual) middleStore
        (.var (ξ (current.length + compilation.administrativePrefix + port.header.slot) + 1))
        (.cellRef (OptionalCell.cellType port.header.named.signature.functionType)
          (owner.key.locations port.header)) middleStore from
        .var (agrees (callerBridge.slots initial port.header port.member))) capture.read
    obtain ⟨returned, _samePool, returnedRelated⟩ := callerBridge.restore initial finalState
      (argumentMaps.trans bodyMaps) (argumentWorlds.trans bodyWorlds)
      (argumentFrame.trans bodyFrame) (argumentMetadata.trans bodyMetadata)
      ((callerBridge.related related).trans bodyRelated)
    refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps,
      argumentMaps.trans bodyMaps, argumentWorlds.trans bodyWorlds,
      argumentFrame.trans bodyFrame, argumentMetadata.trans bodyMetadata, returned, returnedRelated, ?_⟩
    · rw [receipt.emitted, NamedCalls.Arguments.call_rename, ← port.signature, ← port.slot]
      exact SourceCoreCalls.call_success argumentsEvaluated selected bodyEvaluated
    · simpa only [rows.2, nativeResult] using result
    · have rowsStable := CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative
        (callerBridge.pool initial) (callerBridge.pool returned) admitted.rows (argumentFrame.trans bodyFrame)
      cases outcome with
      | value value =>
          refine ⟨rowsStable, ?_⟩
          intro actual same
          cases same
          exact ⟨rows.2 ▸ bodyPost.at_value.1, bodyPost.at_value.2.heap⟩
      | fault failure => cases failure with
          | semantic reason => exact ⟨rowsStable, by intro _ impossible; cases impossible⟩
          | stage origin call reason => exact rowsStable
  · subst outcome
    have argumentsWithin : sequenceSize ≤ size := Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))
    obtain ⟨token, finalStore, finalMap, finalWorld, argumentsEvaluated, matched, finalHeaps,
        maps, worlds, frame, metadata, reached, related, post⟩ :=
      SelectedCompilationExpressionSequence.preserves_fault bridge size sequence unique orderedTyping
        childMeaning environments heaps locals agrees actualTyped initial admitted sourceTrace argumentsWithin
    refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
      maps, worlds, frame, metadata, reached, related, ?_⟩
    · rw [receipt.emitted, NamedCalls.Arguments.call_rename]
      simpa only [receipt.result] using SourceCoreCalls.call_argument_failure
        (signature := receipt.signature) (index := ξ (current.length + compilation.administrativePrefix + receipt.index))
        (internalReason := compilation.internalReason) (receipt.parameter.symm ▸ argumentsEvaluated)
    · exact post.fault
end Preservation

section Reflection
variable {native : SourceCoreGeneralFunctions.CallableContext}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled native)
  (descriptor : SourceCoreCallableContracts.Descriptor native.table (.named port.header.named.signature.key))

include owner receipt port evidenceAt callerBridge functions faults unique certified shaped runtime stagePrepared descriptor in
theorem reflects {children : GenericExpressionMeaning.Certificate}
    (size : Nat)
    (sequence : DataExpressionSequence.Tree invocation.source children scope ids
      (port.header.bindings.map (fun binding => binding.1.scheme.body)) receipt.codes)
    (childMeaning : ReflectsBelow bridge context model (RecursiveNamedPreparedStageScopes.registry stagePrepared)
      invocation children faults size)
    (bodyMeaning : ∀ {child : Staging.Recursive.Scope},
      (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure port.header.function child →
      CallableIndexedOwnedPreparedStagedNamedBodyPorts.ReflectsBelow (headers := headers) (keys := keys)
        port.header model (RecursiveNamedPreparedStageScopes.registry stagePrepared) child faults size) :
    ReflectsAt bridge context model (RecursiveNamedPreparedStageScopes.registry stagePrepared)
      invocation (Point scope id lowered) faults size := by
  intro current child code point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted completed
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans receipt.metadata.found)
  obtain ⟨sourceTypes, calleeValid, application, typing⟩ :=
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.source_types unique receipt.metadata.found
      receipt.form receipt.metadata.coercions typed
  have rows := SelectedCompilationDirectSourceTypes.source_types receipt port.toReady shaped runtime.signatures application
  have orderedTyping := rows.1 ▸ typing
  have nativeResult := result_type receipt port
  have parameter := parameter_type receipt port
  have occurrence : Staging.Recursive.Occurrence invocation child (.call callee ids (.declaration instantiation)) receipt.node.requirements :=
    ⟨receipt.node, lookupExpression?_sound receipt.metadata.found, receipt.form,
      rfl, receipt.metadata.coercions⟩
  obtain ⟨name, calleeOccurrence, valid⟩ :=
    CallableIndexedOwnedPreparedStagedDirectArgumentRows.callee_receipt receipt runtime calleeValid
  rw [receipt.emitted, NamedCalls.Arguments.call_rename, ← port.signature, ← port.slot] at completed
  obtain ⟨sequenceSize, argumentValue, middleStore, smaller, argumentEvaluation⟩ :=
    RecursiveNamedCallBounds.call_arguments completed
  obtain ⟨sourceSize, sourceOutcome, argumentsHeap, middleMap, middleWorld, sourceTrace, represented, middleHeaps,
      argumentMaps, argumentWorlds, argumentFrame, argumentMetadata, reached, related, post⟩ :=
    SelectedCompilationExpressionSequence.reflects bridge size sequence unique orderedTyping childMeaning
      environments heaps locals agrees actualTyped initial admitted argumentEvaluation smaller
  cases represented with
  | fault matched =>
    have evaluated := SourceCoreCalls.call_argument_failure
      (signature := port.header.named.signature)
      (index := ξ (current.length + compilation.administrativePrefix + port.header.slot))
      (internalReason := compilation.internalReason) (parameter.symm ▸ argumentEvaluation.sound)
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound evaluated
    have trace := Staging.Recursive.Size.Expression.directArgumentsFault occurrence calleeOccurrence sourceTrace
    refine ⟨_, _, argumentsHeap, middleMap, middleWorld, trace, ?_, middleHeaps,
      argumentMaps, argumentWorlds, argumentFrame, argumentMetadata, reached, related, ?_⟩
    · rw [← receipt.result, ← port.signature]
      exact .fault matched
    · exact post.fault
  | @values sources values payloads =>
    obtain ⟨parameters, headerHeap, headerArguments, supports⟩ :=
      SelectedCompilationDirectArgumentRows.at_successful_arguments receipt port
        certified runtime post.at_values.heap post.values_typed payloads
    obtain ⟨capture⟩ := CallableIndexedOwnedFunctionEntries.capture_from_pool
      (callerBridge.pool reached) owner port.member
    let nativeCapture := CallableIndexedOwnedFunctionValues.NamedCapture.of_capture capture
    obtain ⟨bodySize, bodySmaller, bodyEvaluation⟩ := RecursiveNamedCallBounds.call_body
      argumentEvaluation.sound (agrees (callerBridge.slots initial port.header port.member)) capture.read completed
    obtain ⟨invocationSize, outcome, after, finalMap, finalWorld, invoked, _bodyEvaluated, result, finalHeaps,
        bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, finalState, bodyRelated, bodyPost⟩ :=
      SelectedCompilationNamedInvocationBounds.reflects_invocation functions owner (callerBridge.pool reached)
        port.header nativeCapture port.prepared port.aligned stagePrepared descriptor port.sourceAt
        port.aligned.layouts port.member certified post.at_values.rows headerHeap headerArguments
        parameters middleHeaps supports size bodyMeaning bodyEvaluation (Nat.le_of_lt bodySmaller)
    have produced := evidenceAt.produces
    have sourceEq := CallableIndexedOwnedPreparedStagedDirectArgumentRows.global_eq receipt port evidenceAt produced
    rw [← sourceEq] at invoked
    have trace := Staging.Recursive.Size.Expression.directApplied occurrence calleeOccurrence valid sourceTrace produced invoked
    obtain ⟨returned, _samePool, returnedRelated⟩ := callerBridge.restore initial finalState
      (argumentMaps.trans bodyMaps) (argumentWorlds.trans bodyWorlds)
      (argumentFrame.trans bodyFrame) (argumentMetadata.trans bodyMetadata)
      ((callerBridge.related related).trans bodyRelated)
    refine ⟨_, outcome, after, finalMap, finalWorld, trace, ?_, finalHeaps,
      argumentMaps.trans bodyMaps, argumentWorlds.trans bodyWorlds,
      argumentFrame.trans bodyFrame, argumentMetadata.trans bodyMetadata, returned, returnedRelated, ?_⟩
    · simpa only [rows.2, nativeResult] using result
    · have rowsStable := CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative
        (callerBridge.pool initial) (callerBridge.pool returned) admitted.rows (argumentFrame.trans bodyFrame)
      cases outcome with
      | value value =>
          refine ⟨rowsStable, ?_⟩
          intro actual same
          cases same
          exact ⟨rows.2 ▸ bodyPost.at_value.1, bodyPost.at_value.2.heap⟩
      | fault failure => cases failure with
          | semantic reason => exact ⟨rowsStable, by intro _ impossible; cases impossible⟩
          | stage origin call reason => exact rowsStable
end Reflection

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationDirectBounds
end
