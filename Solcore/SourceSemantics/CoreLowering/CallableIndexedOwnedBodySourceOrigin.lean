import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyReadyEntries

/-! The original compiler body retains its code, sites, Source and reached
entry. Its visited validity domain also carries authentic Source runtime
facts. The initial receipt supplies these facts; binder extension transports
only the static non-local fields. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodySourceOrigin
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableRuntimeBodyOrigins
universe u v

variable {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {program : Program} (origin : StaticOrigin values ambient registry faults)
  (runtime : Dynamic.SourceRuntimeValid program origin.context origin.function.source)

/-- Strengthening the static domain does not change the compiled body. -/
def source_origin : StaticOrigin values ambient registry faults where
  layouts := origin.layouts
  owner := origin.owner
  active := origin.active
  frameLayout := origin.frameLayout
  globals := origin.globals
  onError := origin.onError
  function := origin.function
  expressionSyntax := origin.expressionSyntax
  certificates := origin.certificates
  validity := fun context => origin.validity context ∧
    Dynamic.SourceRuntimeValid program context origin.function.source
  diagnosticPolicy := origin.diagnosticPolicy
  administrative := origin.administrative
  context := origin.context
  scope := origin.scope
  output := origin.output
  code := origin.code
  fellThrough := origin.fellThrough
  escaped := origin.escaped
  solved := origin.solved
  body := {
    flow := origin.body.flow
    tree := origin.body.tree
    sites := origin.body.sites
    initialValid := ⟨origin.body.initialValid, runtime⟩
    projection := origin.body.projection
    unique := origin.body.unique
    emitted := origin.body.emitted
  }
  definitions := origin.definitions
  registered := origin.registered
  escapedFault := origin.escapedFault
  extend := fun ⟨valid, sourceValid⟩ extended =>
    ⟨origin.extend valid extended,
      sourceValid.transport (Dynamic.RuntimeContextFields.ofBinderExtends extended)⟩
  runtimeOf := fun valid => origin.runtimeOf valid.1

/-- The original complete actual entry is repacked field for field. -/
def entry {Records : Type v} {protocol : ProtectedStateTransition.Protocol.{u, v} Records}
    {condition : Location → CallableIndexedHistory.NativeFrame → Prop}
    {functions : FunctionModel values.checked.catalog ambient}
    (original : Stateful.Entry protocol condition origin functions) :
    Stateful.Entry protocol condition (source_origin origin runtime) functions where
  mapping := original.mapping
  world := original.world
  environment := original.environment
  canonical := original.canonical
  actual := original.actual
  heap := original.heap
  store := original.store
  embedding := original.embedding
  actualContext := original.actualContext
  frameLocation := original.frameLocation
  native := original.native
  environments := original.environments
  heaps := original.heaps
  locals := original.locals
  lookups := original.lookups
  actualTyped := original.actualTyped
  reference := original.reference
  read := original.read
  unmapped := original.unmapped
  initial := original.initial
  gate := original.gate

theorem entry_initial {Records : Type v} {protocol : ProtectedStateTransition.Protocol.{u, v} Records}
    {condition : Location → CallableIndexedHistory.NativeFrame → Prop}
    {functions : FunctionModel values.checked.catalog ambient}
    (original : Stateful.Entry protocol condition origin functions) :
    (entry origin runtime original).initial = original.initial := rfl

theorem source_code : (source_origin origin runtime).code = origin.code := rfl

theorem source_function : (source_origin origin runtime).function = origin.function := rfl

section Owned
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (CallableIndexedOwnedFunctionState.Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {condition : Location → CallableIndexedHistory.NativeFrame → Prop}
  {originalOrigin : StaticOrigin (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) registry faults}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}

def admitted_entry
    (original : CallableIndexedOwnedAdmittedBodyEntries.Entry bridge
      (condition := condition) (origin := originalOrigin) (functions := functions)) :
    CallableIndexedOwnedAdmittedBodyEntries.Entry bridge
      (condition := condition) (origin := source_origin originalOrigin original.source.runtime) (functions := functions) :=
  ⟨entry originalOrigin original.source.runtime original.original, original.source, original.rows⟩

def ready_entry
    (original : CallableIndexedOwnedAdmittedBodyEntries.Entry bridge
      (condition := condition) (origin := originalOrigin) (functions := functions))
    (syntaxTree : GenericImperativeMatch.Syntax originalOrigin.function.source originalOrigin.expressionSyntax originalOrigin.context
      (.statements true originalOrigin.function.body) originalOrigin.function.resultType) :
    CallableRuntimeBodyReadyOrigins.Entry callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge)
      condition (ProtectedStateImperativeTypedSourceSites.Facts originalOrigin.function.source originalOrigin.expressionSyntax)
      (source_origin originalOrigin original.source.runtime) functions :=
  CallableIndexedOwnedBodyReadyEntries.entry bridge (admitted_entry bridge original) syntaxTree

end Owned
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodySourceOrigin
