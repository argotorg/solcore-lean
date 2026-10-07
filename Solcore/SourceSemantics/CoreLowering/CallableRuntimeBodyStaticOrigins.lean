import Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaNestedRuntimeBodyMeaning
import Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodCatalogHookMeaning

/-! Original named, anonymous, and prepared-method static receipts supply the
actual body origins. Reached parameter receipts supply their exact environments
and reads; the actual protected state and its fixed gate remain separate inputs.
These adapters contain no body execution law. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyStaticOrigins
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableAncestryPairedLookup RecursiveNamedCatalog CallableIndexedHistory
open RecursiveNamedCatalogInvocationBounds

universe u v

section Named
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {header : Header prepared values ambient.definitions program}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}

/-- The original named profile retains its complete static flow and source
function. Its context condition uses the profile's original validity mode. -/
def named (runtime : Bool)
    (profile : MatchProfileWith
      (fun context => RecursiveNamedCatalogMutualMeaning.ContextFor runtime header.solved context header.function.evidence)
      certificates diagnosticPolicy header expressionSyntax administrative registry faults)
    (escapedFault : faults .controlEscapedFunction header.escaped) :
    CallableRuntimeBodyOrigins.StaticOrigin values ambient registry faults where
  layouts := header.layouts
  owner := header.owner
  active := header.active
  frameLayout := prepared.layout.frame
  globals := header.globals
  onError := header.onError
  function := header.function
  expressionSyntax := expressionSyntax
  certificates := certificates
  validity := fun context => RecursiveNamedCatalogMutualMeaning.ContextFor runtime header.solved context header.function.evidence
  diagnosticPolicy := diagnosticPolicy
  administrative := administrative
  context := header.context
  scope := header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))
  output := header.output
  code := header.body
  fellThrough := header.fellThrough
  escaped := header.escaped
  solved := header.solved
  body := { flow := profile.flow, tree := profile.tree, sites := profile.errors
            initialValid := profile.initialValid, projection := profile.projection
            unique := header.unique, emitted := profile.emitted }
  definitions := header.definitions_eq
  registered := header.registered
  escapedFault := escapedFault
  extend := fun valid extended => RecursiveNamedCatalogMutualMeaning.context_extend valid extended
  runtimeOf := fun valid => RecursiveNamedCatalogMutualMeaning.context_runtime valid

variable {Records : Type v}
  (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (conditionGate : Location → NativeFrame → Prop)
  {headers : Inventory prepared values ambient.definitions program}
  {locations : Locations (prepared := prepared) (values := values) (ambient := ambient) (program := program)}
  {capturePrefix : Nat} {functions : FunctionModel values.checked.catalog ambient}
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location}
  {current : NativeFrame} {ghost : GhostFrame}

/-- A real reached named body state supplies the original full parameter
layout. The protocol state is supplied at exactly that reached index. -/
def named_entry (runtime : Bool)
    (profile : MatchProfileWith
      (fun context => RecursiveNamedCatalogMutualMeaning.ContextFor runtime header.solved context header.function.evidence)
      certificates diagnosticPolicy header expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)
    (escapedFault : faults .controlEscapedFunction header.escaped)
    (reached : BodyState headers locations capturePrefix functions registry header arguments before initialStore
      initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost)
    (initial : protocol.State ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
      reached.mapping, reached.world, reached.heap, reached.store, reached.canonical⟩)
    (gate : conditionGate frameLocation current) :
    CallableRuntimeBodyOrigins.Stateful.Entry protocol conditionGate (named runtime profile escapedFault) functions where
  mapping := reached.mapping
  world := reached.world
  environment := reached.environment
  canonical := reached.canonical
  actual := reached.actualBody
  heap := reached.heap
  store := reached.store
  embedding := reached.embedding
  actualContext := CallableIndexedParameterTyped.prefixContext header.bindings actualContext
  frameLocation := frameLocation
  native := current
  environments := reached.environments
  heaps := reached.heaps
  locals := reached.locals
  lookups := reached.lookups
  actualTyped := reached.actualTyped
  reference := by simpa only [named, List.length_map, List.length_reverse] using reached.reference
  read := reached.state.read
  unmapped := Eq.mp (congrArg (fun location => location ∉ reached.mapping) reached.catalog_frame)
    reached.catalog.authority.unmapped
  initial := initial
  gate := gate
end Named

section Lambda
variable {values : SourceCoreCompatibleValues.Context}
  {indexed : SourceCoreCallableIndexedPrograms.Prepared values.checked} {program : Program}
  {headers : Inventory indexed.ancestry values indexed.layouts.definitions program}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {function : Dynamic.Closure} {outerScope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : CallableIndexedLambdaValues.Code indexed function outerScope administrative)

/-- The actual named anonymous-body receipt is passed to its existing kernel
projection, including the original source evidence and full captured scope. -/
def lambda_named
    (body : CallableIndexedLambdaNamedRuntimeBodyMeaning.Body headers code program registry faults)
    (escapedFault : faults .controlEscapedFunction code.compilation.internalReason) :
    CallableRuntimeBodyOrigins.StaticOrigin values (CallableIndexedAmbient.ambientDefinitions indexed) registry faults where
  layouts := indexed.layouts
  owner := code.compilation.owner
  active := code.active
  frameLayout := indexed.ancestry.layout.frame
  globals := indexed.base.globals.length
  onError := code.allocationError
  function := function
  expressionSyntax := CallableIndexedLambdaNamedRuntimeBodyMeaning.Nodes function.source
  certificates := fun context => CallableLambdaViewNamedRuntimeCertificates.Certificates
    (ambient := CallableIndexedAmbient.ambientDefinitions indexed) function.evidence headers code.compilation
    body.readFuel function.source context code.compilation.solvedRequirements code.reasonAt
  validity := fun context => CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements context function.evidence
  diagnosticPolicy := .reachable
  administrative := administrative
  context := body.context
  scope := code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ outerScope
  output := code.receipt.resultCore
  code := code.receipt.body
  fellThrough := code.compilation.internalReason
  escaped := code.compilation.internalReason
  solved := code.compilation.solvedRequirements
  body := body.toKernel
  definitions := rfl
  registered := CallableIndexedAmbient.frame_registered indexed
  escapedFault := escapedFault
  extend := fun valid extended => valid.extend extended
  runtimeOf := fun valid => valid

/-- Nested static support keeps the original named caller and rank receipt.
The dynamic source function and evidence remain those of the actual closure. -/
def lambda_nested
    {caller : Header indexed.ancestry values indexed.layouts.definitions program} {rank : Nat}
    (body : CallableIndexedLambdaNestedRuntimeBodyMeaning.Body headers caller registry faults rank code)
    (escapedFault : faults .controlEscapedFunction code.compilation.internalReason) :
    CallableRuntimeBodyOrigins.StaticOrigin values (CallableIndexedAmbient.ambientDefinitions indexed) registry faults where
  layouts := indexed.layouts
  owner := code.compilation.owner
  active := code.active
  frameLayout := indexed.ancestry.layout.frame
  globals := indexed.base.globals.length
  onError := code.allocationError
  function := function
  expressionSyntax := CallableIndexedLambdaNestedRuntimeCertificates.Nodes function.source
  certificates := fun context => CallableIndexedLambdaNestedRuntimeCertificates.Certificates
    (CallableIndexedLambdaNestedRuntimeBodyMeaning.LowerSupport headers caller registry faults rank)
    rank caller headers code.compilation body.body.readFuel function.source context function.evidence
    code.compilation.solvedRequirements code.reasonAt
  validity := fun context => CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements context function.evidence
  diagnosticPolicy := .reachable
  administrative := administrative
  context := body.body.context
  scope := code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ outerScope
  output := code.receipt.resultCore
  code := code.receipt.body
  fellThrough := code.compilation.internalReason
  escaped := code.compilation.internalReason
  solved := code.compilation.solvedRequirements
  body := body.toKernel
  definitions := rfl
  registered := CallableIndexedAmbient.frame_registered indexed
  escapedFault := escapedFault
  extend := fun valid extended => valid.extend extended
  runtimeOf := fun valid => valid

variable {Records : Type v}
  (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (conditionGate : Location → NativeFrame → Prop)
  {functions : FunctionModel values.checked.catalog (CallableIndexedAmbient.ambientDefinitions indexed)}
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location} {native : NativeFrame}

/-- The original anonymous parameter prefix retains the entire captured
source environment and canonical spine at its actual reached state. -/
def lambda_named_entry
    (body : CallableIndexedLambdaNamedRuntimeBodyMeaning.Body headers code program registry faults)
    (escapedFault : faults .controlEscapedFunction code.compilation.internalReason)
    (reached : CallableIndexedLambdaViewPrefix.Entry indexed.ancestry.layout.frame indexed.base.globals.length
      frameLocation native values functions registry function body.context outerScope code.receipt.loweredParameters
      arguments before initialStore initialMap initialWorld administrative actualContext actual ξ code.receipt.allocatedBody code.receipt.body)
    (initial : protocol.State ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ outerScope,
      reached.mapping, reached.world, reached.heap, reached.store, reached.canonical⟩)
    (gate : conditionGate frameLocation native) :
    CallableRuntimeBodyOrigins.Stateful.Entry protocol conditionGate (lambda_named code body escapedFault) functions where
  mapping := reached.mapping
  world := reached.world
  environment := reached.environment
  canonical := reached.canonical
  actual := reached.actualBody
  heap := reached.heap
  store := reached.store
  embedding := reached.embedding
  actualContext := CallableIndexedParameterTyped.prefixContext code.receipt.loweredParameters actualContext
  frameLocation := frameLocation
  native := native
  environments := reached.environments
  heaps := reached.heaps
  locals := reached.locals
  lookups := reached.lookups
  actualTyped := reached.actualTyped
  reference := reached.reference
  read := reached.read
  unmapped := reached.unmapped
  initial := initial
  gate := gate

/-- Nested anonymous entry uses the same full prefix receipt at the exact
context retained by its original nested static body. -/
def lambda_nested_entry
    {caller : Header indexed.ancestry values indexed.layouts.definitions program} {rank : Nat}
    (body : CallableIndexedLambdaNestedRuntimeBodyMeaning.Body headers caller registry faults rank code)
    (escapedFault : faults .controlEscapedFunction code.compilation.internalReason)
    (reached : CallableIndexedLambdaViewPrefix.Entry indexed.ancestry.layout.frame indexed.base.globals.length
      frameLocation native values functions registry function body.body.context outerScope code.receipt.loweredParameters
      arguments before initialStore initialMap initialWorld administrative actualContext actual ξ code.receipt.allocatedBody code.receipt.body)
    (initial : protocol.State ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ outerScope,
      reached.mapping, reached.world, reached.heap, reached.store, reached.canonical⟩)
    (gate : conditionGate frameLocation native) :
    CallableRuntimeBodyOrigins.Stateful.Entry protocol conditionGate (lambda_nested code body escapedFault) functions where
  mapping := reached.mapping
  world := reached.world
  environment := reached.environment
  canonical := reached.canonical
  actual := reached.actualBody
  heap := reached.heap
  store := reached.store
  embedding := reached.embedding
  actualContext := CallableIndexedParameterTyped.prefixContext code.receipt.loweredParameters actualContext
  frameLocation := frameLocation
  native := native
  environments := reached.environments
  heaps := reached.heaps
  locals := reached.locals
  lookups := reached.lookups
  actualTyped := reached.actualTyped
  reference := reached.reference
  read := reached.read
  unmapped := reached.unmapped
  initial := initial
  gate := gate
end Lambda

section Method
variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {outputCode : Expr}
  (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics outputCode)
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {sourceBody : Dynamic.BodyInstance} {dictionary : Dynamic.EvidenceEnvironment}
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {validity : SourceSemantics.Context → Prop} {diagnosticPolicy : AssignmentDiagnosticPolicy}

/-- Method attribution keeps the raw source body and full dictionary separate
from the named compilation metadata. Only the actual static profile is used. -/
def method
    (profile : CallablePreparedMethodCatalogHookMeaning.ProfileFor compiled values ambient sourceBody dictionary
      administrative registry faults expressionSyntax certificates validity diagnosticPolicy)
    (escapedFault : faults .controlEscapedFunction compiled.own.table.escapedReason)
    (extend : ∀ {context next binder}, validity context → BinderExtends sourceBody.source.owner context binder next → validity next)
    (runtimeOf : ∀ {context}, validity context →
      CompatibleRuntimeContextValidity.Valid named.specialized.function.solvedRequirements context dictionary) :
    CallableRuntimeBodyOrigins.StaticOrigin values ambient registry faults where
  layouts := prepared.layouts
  owner := named.signature.key
  active := []
  frameLayout := prepared.ancestry.layout.frame
  globals := prepared.base.globals.length
  onError := fun error => .sourceAllocation (reprStr error)
  function := CallablePreparedMethodRuntimeMeaning.methodFunction compiled sourceBody dictionary
  expressionSyntax := expressionSyntax
  certificates := certificates
  validity := validity
  diagnosticPolicy := diagnosticPolicy
  administrative := SourceCoreCompatibleCatalog.packTypes (named.inputs.map Prod.snd) :: administrative
  context := profile.context
  scope := named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))
  output := named.signature.resultType
  code := compiled.body
  fellThrough := compiled.own.fellThroughReason
  escaped := compiled.own.table.escapedReason
  solved := named.specialized.function.solvedRequirements
  body := profile.body
  definitions := profile.definitions
  registered := profile.registered
  escapedFault := escapedFault
  extend := extend
  runtimeOf := runtimeOf

/-- The existing builtin method kernel supplies the same pure static adapter. -/
def method_builtin
    (profile : CallablePreparedMethodRuntimeMeaning.Profile compiled values ambient sourceBody dictionary
      administrative registry faults)
    (escapedFault : faults .controlEscapedFunction compiled.own.table.escapedReason) :
    CallableRuntimeBodyOrigins.StaticOrigin values ambient registry faults :=
  method compiled (CallablePreparedMethodCatalogHookMeaning.of_builtin compiled profile) escapedFault
    (fun valid extended => valid.extend extended) (fun valid => valid)

variable {Records : Type v}
  (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (conditionGate : Location → NativeFrame → Prop)
  {functions : FunctionModel values.checked.catalog ambient}
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location} {native : NativeFrame}

/-- The actual mixed named parameter receipt supplies every dynamic method
entry field. The independent dictionary and source frame stay in the profile. -/
def method_entry
    (profile : CallablePreparedMethodCatalogHookMeaning.ProfileFor compiled values ambient sourceBody dictionary
      administrative registry faults expressionSyntax certificates validity diagnosticPolicy)
    (escapedFault : faults .controlEscapedFunction compiled.own.table.escapedReason)
    (extend : ∀ {context next binder}, validity context → BinderExtends sourceBody.source.owner context binder next → validity next)
    (runtimeOf : ∀ {context}, validity context →
      CompatibleRuntimeContextValidity.Valid named.specialized.function.solvedRequirements context dictionary)
    (reached : TypedMixedNamedParameters.Entry prepared.ancestry.layout.frame prepared.base.globals.length
      frameLocation native values functions registry (CallablePreparedMethodRuntimeMeaning.methodFunction compiled sourceBody dictionary)
      profile.context named.inputs arguments before initialStore initialMap initialWorld administrative actualContext
      actual ξ compiled.parameterCode compiled.body)
    (initial : protocol.State ⟨named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      reached.mapping, reached.world, reached.heap, reached.store, reached.canonical⟩)
    (gate : conditionGate frameLocation native) :
    CallableRuntimeBodyOrigins.Stateful.Entry protocol conditionGate
      (method compiled profile escapedFault extend runtimeOf) functions where
  mapping := reached.mapping
  world := reached.world
  environment := reached.environment
  canonical := reached.canonical
  actual := reached.actualBody
  heap := reached.heap
  store := reached.store
  embedding := reached.embedding
  actualContext := CallableIndexedParameterTyped.prefixContext named.inputs actualContext
  frameLocation := frameLocation
  native := native
  environments := reached.environments
  heaps := reached.heaps
  locals := reached.locals
  lookups := reached.lookups
  actualTyped := reached.actualTyped
  reference := reached.reference
  read := reached.read
  unmapped := reached.unmapped
  initial := initial
  gate := gate
/-- A reached builtin method profile uses its original kernel projection and
parameter receipt at the same raw source context and dictionary. -/
def method_builtin_entry
    (profile : CallablePreparedMethodRuntimeMeaning.Profile compiled values ambient sourceBody dictionary
      administrative registry faults)
    (escapedFault : faults .controlEscapedFunction compiled.own.table.escapedReason)
    (reached : TypedMixedNamedParameters.Entry prepared.ancestry.layout.frame prepared.base.globals.length
      frameLocation native values functions registry (CallablePreparedMethodRuntimeMeaning.methodFunction compiled sourceBody dictionary)
      profile.context named.inputs arguments before initialStore initialMap initialWorld administrative actualContext
      actual ξ compiled.parameterCode compiled.body)
    (initial : protocol.State ⟨named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      reached.mapping, reached.world, reached.heap, reached.store, reached.canonical⟩)
    (gate : conditionGate frameLocation native) :
    CallableRuntimeBodyOrigins.Stateful.Entry protocol conditionGate
      (method_builtin compiled profile escapedFault) functions :=
  method_entry compiled protocol conditionGate
    (CallablePreparedMethodCatalogHookMeaning.of_builtin compiled profile) escapedFault
    (fun valid extended => valid.extend extended) (fun valid => valid) reached initial gate
end Method

end Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyStaticOrigins
