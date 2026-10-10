import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogIndirectInvocationDispatcher
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureSourceArguments

/-! The actual admitted argument post supplies independent Source heap and
argument typing. These constructors combine that typing with the genuine
retained closure or global compiler leaf. No flow, body meaning or execution
outcome is an input to the application receipt. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogIndirectArgumentReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey NamedSourceAt NamedCapture)
open CallableIndexedOwnedPreparedContextualQualification (Facet)
open CallableIndexedOwnedPreparedNativeDirectCellOrigins (Association)
open CallableIndexedOwnedPreparedCatalogIndirectInvocationDispatcher (Receipt)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {qualification : Facet compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {certificates : Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {context : SourceSemantics.Context} {source : TypedSource}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {index : ProtectedStateTransition.Index} (initial : callerProtocol.State index)
  (admitted : Admission bridge context initial)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  {calleeHeap : Dynamic.Heap} {arguments : List Dynamic.Value} {payloads : List Value}
  {types : List TypeSystem.Ty} {parameter result : TypeSystem.Ty} {packed : Dynamic.Value}
  (extension : Dynamic.HeapTypesExtend calleeHeap index.heap)
  (argumentsTyped : Dynamic.ValuesHaveTypes context index.heap arguments types)
  (packing : Dynamic.ValuesPack arguments packed)
  (bundle : TypeSystem.Ty.productMany types = parameter)

include bridge initial admitted runtime extension argumentsTyped packing bundle in
/-- Raw Source closure admission is reconstructed at this actual argument
heap, after its genuine Source type extension. The stored Code is unchanged. -/
theorem closure {function : Dynamic.Closure} {native : Value}
    {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}
    (member : Association qualification headers keys bodyRegistry faults
      index.mapping index.world function native bindings parameterCore resultCore)
    (calleeTyped : Dynamic.ValueHasType context calleeHeap (.closure function) (.function parameter result))
    (represented : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      index.mapping index.world bindings arguments payloads) :
    Receipt (qualification := qualification) (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (mapping := index.mapping) (world := index.world) (before := index.heap) (arguments := arguments) (payloads := payloads)
      functions (.closure function) function.evidence native function.resultType resultCore := by
  have count : bindings.length = function.parameters.length := by
    simpa only [List.length_map] using congrArg List.length member.source_binders
  have arity : arguments.length = function.parameters.length := represented.length.1.symm.trans count
  obtain ⟨raw, _rows⟩ := CallableIndexedOwnedStoredClosureSourceArguments.after_argument_extension
    bridge initial runtime admitted calleeTyped extension argumentsTyped packing bundle arity
  exact .closure member represented raw.heaps raw.arguments raw.captures

include bridge initial admitted runtime extension argumentsTyped packing bundle in
/-- The genuine global SourceFrame and dictionary transport the packed raw
argument typing into the retained Header context at the same reached heap. -/
theorem named {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {function : Dynamic.GlobalFunction}
    (owner : OwnedKey keys) (member : header ∈ headers)
    (captureZero : owner.key.capturePrefix = 0)
    (globals : header.globals = compiled.indexed.base.globals.length)
    (sourceAt : NamedSourceAt header rawD function)
    (capture : NamedCapture headers owner.key header index.mapping index.world)
    (identity descriptor : Word) (sameLayouts : header.layouts = compiled.indexed.layouts)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (calleeTyped : Dynamic.ValueHasType context calleeHeap (.global function) (.function parameter result))
    (represented : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      index.mapping index.world header.bindings arguments payloads)
    (profiles : CallableIndexedOwnedPreparedCatalogNamedBodyContinuations.ProfilesFor
      (headers := headers) (registry := registry) (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions owner (header := header))
    (syntaxTree : GenericImperativeMatch.Syntax header.function.source (expressionSyntax header)
      header.context (.statements true header.function.body) header.function.resultType) :
    Receipt (qualification := qualification) (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (mapping := index.mapping) (world := index.world) (before := index.heap) (arguments := arguments) (payloads := payloads)
      functions (.global function) function.evidence
      (CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds.carrier owner capture identity descriptor)
      header.function.resultType header.output := by
  have arity : header.function.parameters.length = arguments.length :=
    (congrArg List.length header.parameters).trans ((List.length_map Prod.fst).trans represented.length.1)
  have packedTyped : Dynamic.ValueHasType context index.heap packed parameter :=
    bundle ▸ packing.hasType argumentsTyped
  obtain ⟨heapTyped, rawTyped⟩ :=
    CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds.arguments_at_global
      sourceAt wellFormed runtime admitted.heap (calleeTyped.mono extension) packing packedTyped arity
  exact .named owner member captureZero globals sourceAt capture identity descriptor represented
    heapTyped rawTyped sameLayouts profiles syntaxTree

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogIndirectArgumentReceipts
