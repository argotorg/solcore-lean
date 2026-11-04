import Solcore.SourceSemantics.CoreLowering.Internal.Callable.RuntimeBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaRuntime
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.PreparedMethods
import Solcore.Frontend.SourceCoreGeneralFunctions
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.CoreEvaluation
import Solcore.Frontend.SourceCoreCallableContracts
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.BasicExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.AssignmentContracts
import Solcore.Frontend.SourceCoreCallableFaultSites
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Paths
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.LambdaViewTrees
import Solcore.SourceSemantics.Graph
import Solcore.Frontend.SourceInference.TypedIRProperties
import Solcore.SourceSemantics.Staging.CallBoundary
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.SourceExecutionSize

/-!
# Callable runtime: indirect calls

Certificates and bounds of indirect calls, body metadata views, view substitution, and the runtime named body family.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyStaticOrigins
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
      arguments before initialStore initialMap initialWorld administrative actualContext actual ξ code.receipt.copiedBody code.receipt.body)
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
  actualContext := CallableIndexedParameterTyped.prefixContext code.receipt.loweredParameters reached.copiedContext
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
      arguments before initialStore initialMap initialWorld administrative actualContext actual ξ code.receipt.copiedBody code.receipt.body)
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
  actualContext := CallableIndexedParameterTyped.prefixContext code.receipt.loweredParameters reached.copiedContext
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndirectCallCertificates
/-! Actual indirect lowering receipts. Parent special-hook delegation and both
source lookups remain explicit: an arbitrary policy can observe a different
source node. The actual callee and ordered argument compiler vector share the
same remaining fuel. No source or called-body execution law is stored here. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndirectCallCertificates
open Core Frontend SourceInference
abbrev Scope := SourceCoreBasic.Scope
abbrev LoweredExpr := SourceCoreBasic.LoweredExpr

structure Receipt (policy : SourceCoreFunctions.Policy) (body : SourceCoreFunctions.BodyLowerer)
    (fuel : Nat) (compilation : SourceCoreFunctions.Context) (source : TypedSource) (scope : Scope)
    (id callee : ExpressionId) (arguments : List ExpressionId) (metadata : IndirectCallResolution)
    (reasonAt : ExpressionId → Word) (lowered : LoweredExpr) where
  accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1) compilation source scope id reasonAt = .ok lowered
  specialDelegation : ∀ child budget, (match policy.lowerSpecial? with
    | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
    | some lower => lower compilation child budget source scope id reasonAt) = .ok none
  original : ExpressionNode
  found : source.lookupExpression? id = some original
  originalForm : original.form = .call callee arguments (.indirect metadata)
  owned : id.occurrence.owner = source.owner
  node : ExpressionNode
  type : Ty
  read : policy.readExpression source id = .ok (node, type)
  form : node.form = .call callee arguments (.indirect metadata)
  argumentCoercions : metadata.argumentCoercions = []
  validated : SourceCompilationPlan.validateIndirectCallMetadata source node callee arguments metadata = .ok ()
  calleeNode : ExpressionNode
  calleeReadType : Ty
  calleeRead : policy.readExpression source callee = .ok (calleeNode, calleeReadType)
  parameter : TypeSystem.Ty
  result : TypeSystem.Ty
  calleeType : calleeNode.type = .function parameter result
  parameterType : Ty
  resultType : Ty
  parameterProject : policy.projectType (.occurrence id.occurrence) parameter = .ok parameterType
  resultProject : policy.projectType (.occurrence id.occurrence) result = .ok resultType
  resultTypeEq : resultType = type
  calleeCode : LoweredExpr
  codes : List LoweredExpr
  calleeAccepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope callee reasonAt = .ok calleeCode
  argumentsAccepted : arguments.mapM (fun child => SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope child reasonAt) = .ok codes
  packedType : parameterType = (SourceCoreCalls.packArguments codes).type
  callableType : policy.callables.functionType parameterType resultType = calleeCode.type
  expression : Expr
  hook : policy.callables.callCallable compilation source node resultType calleeCode.expression (SourceCoreCalls.packArguments codes).expression = .ok expression
  output : lowered = ⟨type, expression⟩

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem ensure_type {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  by_cases same : expected = actual
  · exact same
  · simp [SourceCoreBasic.ensureType, same] at accepted

/-- The receipt comes from the actual successful branch. It retains both
original and policy-read nodes without claiming their full metadata equality. -/
theorem of_functions {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : Scope}
    {id callee : ExpressionId} {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    {reasonAt : ExpressionId → Word} {lowered : LoweredExpr} {original node : ExpressionNode} {type : Ty}
    (found : source.lookupExpression? id = some original)
    (originalForm : original.form = .call callee arguments (.indirect metadata))
    (special : ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation child budget source scope id reasonAt) = .ok none)
    (read : policy.readExpression source id = .ok (node, type))
    (form : node.form = .call callee arguments (.indirect metadata))
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1) compilation source scope id reasonAt = .ok lowered) :
    Nonempty (Receipt policy body fuel compilation source scope id callee arguments metadata reasonAt lowered) := by
  have originalAccepted := accepted
  have originalSpecial := special
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  by_cases owned : id.occurrence.owner = source.owner
  · simp only [owned, ne_eq, not_true_eq_false, ↓reduceIte, found, bind, Except.bind, pure, Except.pure] at accepted
    have bypass := special (fun budget childSource childScope childId childReasonAt =>
      SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel) compilation childSource childScope childId childReasonAt) (fuel + 1)
    cases hook : policy.lowerSpecial? <;> simp only [hook] at accepted bypass
    all_goals try rw [bypass] at accepted
    all_goals
      simp only [originalForm, read, form, bind, Except.bind, pure, Except.pure] at accepted
      by_cases empty : metadata.argumentCoercions.isEmpty = true
      · simp only [empty, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure, Except.pure, bind, Except.bind] at accepted
        obtain ⟨checked, validated, accepted⟩ := bind_ok accepted
        cases checked
        obtain ⟨pair, calleeRead, accepted⟩ := bind_ok accepted
        obtain ⟨calleeNode, calleeReadType⟩ := pair
        cases calleeType : calleeNode.type <;> simp only [calleeType] at accepted
        all_goals try cases accepted
        rename_i parameter result
        obtain ⟨parameterType, parameterProject, accepted⟩ := bind_ok accepted
        obtain ⟨resultType, resultProject, accepted⟩ := bind_ok accepted
        obtain ⟨checked, resultChecked, accepted⟩ := bind_ok accepted
        cases checked
        obtain ⟨calleeCode, calleeAccepted, accepted⟩ := bind_ok accepted
        obtain ⟨codes, argumentsAccepted, accepted⟩ := bind_ok accepted
        obtain ⟨checked, packedChecked, accepted⟩ := bind_ok accepted
        cases checked
        obtain ⟨checked, callableChecked, accepted⟩ := bind_ok accepted
        cases checked
        obtain ⟨expression, callAccepted, accepted⟩ := bind_ok accepted
        cases accepted
        have actualValidated : SourceCompilationPlan.validateIndirectCallMetadata source node callee arguments metadata = .ok () := by
          cases h : SourceCompilationPlan.validateIndirectCallMetadata source node callee arguments metadata <;> simp_all [Except.mapError]
        exact ⟨{ accepted := originalAccepted, specialDelegation := originalSpecial
                 original, found, originalForm, owned, node, type, read, form
                 argumentCoercions := List.isEmpty_iff.mp empty
                 validated := actualValidated, calleeNode, calleeReadType, calleeRead
                 parameter, result, calleeType, parameterType, resultType, parameterProject, resultProject
                 resultTypeEq := ensure_type resultChecked, calleeCode, codes, calleeAccepted, argumentsAccepted
                 packedType := ensure_type packedChecked, callableType := ensure_type callableChecked
                 expression, hook := callAccepted, output := rfl }⟩
      · simp [empty] at accepted
  · simp [owned, bind, Except.bind] at accepted

private theorem mapM_ordered {α β ε : Type} {ids : List α} {codes : List β}
    {compile : α → Except ε β} (accepted : ids.mapM compile = .ok codes) :
    ids.length = codes.length ∧ ∀ id code, (id, code) ∈ ids.zip codes → compile id = .ok code := by
  induction ids generalizing codes with
  | nil =>
      simp only [List.mapM_nil, pure, Except.pure] at accepted
      cases accepted
      exact ⟨rfl, by simp⟩
  | cons head tail ih =>
      simp only [List.mapM_cons] at accepted
      obtain ⟨headCode, headAccepted, accepted⟩ := bind_ok accepted
      obtain ⟨tailCodes, tailAccepted, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨length, children⟩ := ih tailAccepted
      refine ⟨by simp only [List.length_cons, length], ?_⟩
      intro id code member
      rcases List.mem_cons.mp member with same | remaining
      · cases same; exact headAccepted
      · exact children id code remaining

/-- The vector retains physical order and duplicates. Each pair refers to the
same compiler invocation and same fuel, including the leading callee. -/
def Receipt.entries {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : Scope}
    {id callee : ExpressionId} {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    {reasonAt : ExpressionId → Word} {lowered : LoweredExpr}
    (receipt : Receipt policy body fuel compilation source scope id callee arguments metadata reasonAt lowered) :
    List (ExpressionId × LoweredExpr) := (callee, receipt.calleeCode) :: arguments.zip receipt.codes

theorem Receipt.ordered_children {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : Scope}
    {id callee : ExpressionId} {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    {reasonAt : ExpressionId → Word} {lowered : LoweredExpr}
    (receipt : Receipt policy body fuel compilation source scope id callee arguments metadata reasonAt lowered) :
    arguments.length = receipt.codes.length ∧ ∀ child code, (child, code) ∈ receipt.entries →
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope child reasonAt = .ok code := by
  obtain ⟨length, children⟩ := mapM_ordered receipt.argumentsAccepted
  refine ⟨length, ?_⟩
  intro child code member
  rcases List.mem_cons.mp member with same | remaining
  · cases same; exact receipt.calleeAccepted
  · exact children child code remaining

/-- The actual general callable policy recovers its prepared table row, rather
than replacing an arbitrary hook with a contract expression. -/
theorem Receipt.prepared_site {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : Scope}
    {id callee : ExpressionId} {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    {reasonAt : ExpressionId → Word} {lowered : LoweredExpr}
    (receipt : Receipt policy body fuel compilation source scope id callee arguments metadata reasonAt lowered)
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (actualPolicy : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active) :
    ∃ site, SourceCoreCallableContracts.prepareCallsite native.table compilation.owner receipt.node.id native.diagnostics.reasonAt = .ok site ∧
      site.table = native.table ∧ site.caller = compilation.owner ∧ site.call = receipt.node.id ∧
      receipt.expression = site.lower native.diagnostics.unknown receipt.resultType receipt.calleeCode.expression (SourceCoreCalls.packArguments receipt.codes).expression := by
  have accepted := receipt.hook
  rw [actualPolicy] at accepted
  simp only [SourceCoreGeneralFunctions.callablePolicy, receipt.form, bind, Except.bind, pure, Except.pure] at accepted
  cases prepared : SourceCoreCallableContracts.prepareCallsite native.table compilation.owner receipt.node.id native.diagnostics.reasonAt with
  | error => simp [prepared, Except.mapError] at accepted
  | ok site =>
      simp only [prepared, Except.mapError, bind, Except.bind, pure, Except.pure] at accepted
      have expressionEq := (Except.ok.inj accepted).symm
      refine ⟨site, rfl, ?_, ?_, ?_, expressionEq⟩
      all_goals unfold SourceCoreCallableContracts.prepareCallsite at prepared
      all_goals split at prepared
      all_goals first | cases prepared; rfl | cases prepared

end Solcore.SourceSemantics.CoreLowering.CallableIndirectCallCertificates
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndirectCallBounds
/-! Original Core completion of the actual two-guard indirect call protocol.
Every child grade comes from the supplied evaluation. The guard tokens and
all intermediate stores remain explicit until actual callable representation
identifies the tokens. No called-body or source execution law is assumed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndirectCallBounds
open Core CoreProof Frontend.SourceCoreCallableContracts

inductive BindCompletion (budget : Nat) (environment : Core.Environment)
    (before : Store) (output : Ty) (computation body : Expr) : Value → Store → Prop where
  | failed {size : Nat} {input : Ty} {payload : Value} {after : Store}
      (child : EvaluationSize size environment before computation (.inLeft input payload) after)
      (strict : size < budget) :
      BindCompletion budget environment before output computation body (.inLeft output payload) after
  | continued {childSize bodySize : Nat} {input : Ty} {payload : Value} {middle after : Store} {value : Value}
      (child : EvaluationSize childSize environment before computation (.inRight input payload) middle)
      (bodyTrace : EvaluationSize bodySize (payload :: environment) middle body value after)
      (childStrict : childSize < budget) (bodyStrict : bodySize < budget) :
      BindCompletion budget environment before output computation body value after

/-- Invert the existing sum case; the failure branch is its original var read. -/
theorem bind_completed {size budget : Nat} {environment : Core.Environment} {before after : Store}
    {output : Ty} {computation body : Expr} {value : Value}
    (evaluation : EvaluationSize size environment before
      (LanguageResult.bind output computation body) value after)
    (within : size ≤ budget) :
    BindCompletion budget environment before output computation body value after := by
  cases evaluation with
  | caseLeft child failure =>
      cases failure with
      | inLeft payload =>
          cases payload with
          | var selected =>
              simp only [List.getElem?_cons_zero] at selected
              cases Option.some.inj selected
              exact .failed child (by omega)
  | caseRight child body => exact .continued child body (by omega) (by omega)

/-- The four successive binds expose the exact hidden environment prefixes. -/
inductive Completion (budget : Nat) (gates : List CallableContract.Gate) (unknown : Word)
    (result : Ty) (callee arguments : Expr) (environment : Core.Environment) (before : Store) :
    Value → Store → Prop where
  | calleeFailure {size : Nat} {input : Ty} {payload : Value} {after : Store}
      (calleeTrace : EvaluationSize size environment before callee (.inLeft input payload) after)
      (strict : size < budget) : Completion budget gates unknown result callee arguments environment before
        (.inLeft result payload) after
  | stageRejected {calleeSize gateSize : Nat} {input gateInput : Ty}
      {function fault : Value} {calleeStore after : Store}
      (calleeTrace : EvaluationSize calleeSize environment before callee (.inRight input function) calleeStore)
      (gate : EvaluationSize gateSize (function :: environment) calleeStore
        (CallableContract.dispatch gates .beforeArguments unknown (.second (.var 0)))
        (.inLeft gateInput fault) after)
      (calleeStrict : calleeSize < budget) (gateStrict : gateSize < budget) :
      Completion budget gates unknown result callee arguments environment before (.inLeft result fault) after
  | argumentFailure {calleeSize gateSize argumentsSize : Nat} {input gateInput argumentInput : Ty}
      {function token fault : Value} {calleeStore argumentStore after : Store}
      (calleeTrace : EvaluationSize calleeSize environment before callee (.inRight input function) calleeStore)
      (gate : EvaluationSize gateSize (function :: environment) calleeStore
        (CallableContract.dispatch gates .beforeArguments unknown (.second (.var 0)))
        (.inRight gateInput token) argumentStore)
      (argumentsTrace : EvaluationSize argumentsSize (token :: function :: environment) argumentStore
        ((arguments.weakenAt 0).weakenAt 0) (.inLeft argumentInput fault) after)
      (calleeStrict : calleeSize < budget) (gateStrict : gateSize < budget)
      (argumentsStrict : argumentsSize < budget) :
      Completion budget gates unknown result callee arguments environment before (.inLeft result fault) after
  | arityRejected {calleeSize gateSize argumentsSize aritySize : Nat}
      {input gateInput argumentInput arityInput : Ty} {function token argument fault : Value}
      {calleeStore argumentStore arityStore after : Store}
      (calleeTrace : EvaluationSize calleeSize environment before callee (.inRight input function) calleeStore)
      (gate : EvaluationSize gateSize (function :: environment) calleeStore
        (CallableContract.dispatch gates .beforeArguments unknown (.second (.var 0)))
        (.inRight gateInput token) argumentStore)
      (argumentsTrace : EvaluationSize argumentsSize (token :: function :: environment) argumentStore
        ((arguments.weakenAt 0).weakenAt 0) (.inRight argumentInput argument) arityStore)
      (arity : EvaluationSize aritySize (argument :: token :: function :: environment) arityStore
        (CallableContract.dispatch gates .beforeApplication unknown (.second (.var 2)))
        (.inLeft arityInput fault) after)
      (calleeStrict : calleeSize < budget) (gateStrict : gateSize < budget)
      (argumentsStrict : argumentsSize < budget) (arityStrict : aritySize < budget) :
      Completion budget gates unknown result callee arguments environment before (.inLeft result fault) after
  | applied {calleeSize gateSize argumentsSize aritySize functionSize parameterSize bodySize : Nat}
      {input gateInput argumentInput arityInput parameter resultType : Ty}
      {function token argument arityToken parameterValue value : Value}
      {captured : Core.Environment} {body : Expr}
      {calleeStore argumentStore arityStore applicationStore parameterStore bodyStore after : Store}
      (calleeTrace : EvaluationSize calleeSize environment before callee (.inRight input function) calleeStore)
      (gate : EvaluationSize gateSize (function :: environment) calleeStore
        (CallableContract.dispatch gates .beforeArguments unknown (.second (.var 0)))
        (.inRight gateInput token) argumentStore)
      (argumentsTrace : EvaluationSize argumentsSize (token :: function :: environment) argumentStore
        ((arguments.weakenAt 0).weakenAt 0) (.inRight argumentInput argument) arityStore)
      (arity : EvaluationSize aritySize (argument :: token :: function :: environment) arityStore
        (CallableContract.dispatch gates .beforeApplication unknown (.second (.var 2)))
        (.inRight arityInput arityToken) applicationStore)
      (functionTrace : EvaluationSize functionSize (arityToken :: argument :: token :: function :: environment) applicationStore
        (.second (.first (.var 3))) (.closure parameter resultType body captured) parameterStore)
      (parameterTrace : EvaluationSize parameterSize (arityToken :: argument :: token :: function :: environment) parameterStore
        (.var 1) parameterValue bodyStore)
      (bodyTrace : EvaluationSize bodySize (parameterValue :: captured) bodyStore body value after)
      (calleeStrict : calleeSize < budget) (gateStrict : gateSize < budget)
      (argumentsStrict : argumentsSize < budget) (arityStrict : aritySize < budget)
      (functionStrict : functionSize < budget) (parameterStrict : parameterSize < budget)
      (bodyStrict : bodySize < budget) :
      Completion budget gates unknown result callee arguments environment before value after

theorem call_completed {size budget : Nat} {environment : Core.Environment} {before after : Store}
    {gates : List CallableContract.Gate} {unknown : Word} {result : Ty} {callee arguments : Expr} {value : Value}
    (evaluation : EvaluationSize size environment before (CallableContract.call gates unknown result callee arguments) value after)
    (within : size ≤ budget) : Completion budget gates unknown result callee arguments environment before value after := by
  cases bind_completed evaluation within with
  | failed callee strict => exact .calleeFailure callee strict
  | continued callee remaining calleeStrict remainingStrict =>
      cases bind_completed remaining (Nat.le_of_lt remainingStrict) with
      | failed gate strict => exact .stageRejected callee gate calleeStrict strict
      | continued gate remaining gateStrict remainingStrict =>
          cases bind_completed remaining (Nat.le_of_lt remainingStrict) with
          | failed arguments strict => exact .argumentFailure callee gate arguments calleeStrict gateStrict strict
          | continued arguments remaining argumentsStrict remainingStrict =>
              cases bind_completed remaining (Nat.le_of_lt remainingStrict) with
              | failed arity strict => exact .arityRejected callee gate arguments arity calleeStrict gateStrict argumentsStrict strict
              | continued arity application arityStrict applicationStrict =>
                  cases application with
                  | apply function parameter body =>
                      exact .applied callee gate arguments arity function parameter body calleeStrict gateStrict
                        argumentsStrict arityStrict (by omega) (by omega) (by omega)

/-- The actual projection/var children determine the original closure and
argument, including the complete captured suffix. Only those pure reads are
identified; the body is the original graded child. -/
theorem application_completed {size budget : Nat} {environment : Core.Environment}
    {before after : Store} {function token argument arityToken value : Value}
    (evaluation : EvaluationSize size (arityToken :: argument :: token :: function :: environment) before
      (.apply (.second (.first (.var 3))) (.var 1)) value after)
    (within : size ≤ budget) :
    ∃ identity contract parameter result body captured bodySize,
      function = .pair (.pair identity (.closure parameter result body captured)) contract ∧
      bodySize < budget ∧ EvaluationSize bodySize (argument :: captured) before body value after := by
  cases evaluation with
  | apply selected parameter body =>
      cases selected with
      | second tagged =>
          cases tagged with
          | first lookup =>
              cases lookup with
              | var found =>
                  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at found
                  cases Option.some.inj found
                  cases parameter with
                  | var read =>
                      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at read
                      cases Option.some.inj read
                      exact ⟨_, _, _, _, _, _, _, rfl, by omega, body⟩

/-- Actual prepared site lowering uses the same completion with the same rows. -/
theorem Callsite.completed {size budget : Nat} {environment : Core.Environment} {before after : Store}
    {site : Callsite} {unknown : Word} {result : Ty} {callee arguments : Expr} {value : Value}
    (evaluation : EvaluationSize size environment before (site.lower unknown result callee arguments) value after)
    (within : size ≤ budget) : Completion budget site.gates unknown result callee arguments environment before value after :=
  call_completed evaluation within

/-- Pure dispatch identifies its result and store from an explicit native word
read. It does not identify source origin, history, or authority. -/
theorem dispatch_decision {size : Nat} {environment : Core.Environment} {before after : Store}
    {gates : List CallableContract.Gate} {phase : CallableContract.Phase} {unknown contract : Word}
    {expression : Expr} {value : Value}
    (read : Evaluates environment before expression (.word contract) before)
    (evaluation : EvaluationSize size environment before
      (CallableContract.dispatch gates phase unknown expression) value after) :
    value = CallableContract.resultValue (CallableContract.decision gates phase unknown contract) ∧ after = before :=
  (CallableContract.dispatch_iff gates phase unknown contract read).mp evaluation.sound

/-- A native rejected gate and the independent actual source dispatch recover
the exact staged-source rejection. Arguments have not been evaluated here.
The conclusion is GuardRejects, with no projection to plain Dynamic. -/
theorem stage_rejection {size : Nat} {environment : Core.Environment} {before after : Store}
    {frame : Staging.CallBoundary.Frame} {site : Callsite}
    {call : Frontend.SourceInference.ExpressionId} {arguments : List Frontend.SourceInference.ExpressionId}
    {source : Dynamic.Value} {carrier : Value} {unknown token : Word} {input : Ty}
    (dispatch : CallStageBoundary.Dispatch frame site call arguments source carrier)
    (evaluation : EvaluationSize size (carrier :: environment) before
      (CallableContract.dispatch site.gates .beforeArguments unknown (.second (.var 0)))
      (.inLeft input (.word token)) after) :
    ∃ reason, Staging.CallBoundary.GuardRejects frame call arguments source reason ∧
      CallStageBoundary.ReasonRepresents site reason token ∧ after = before := by
  have read : Evaluates (carrier :: environment) before (.second (.var 0)) (.word dispatch.contract) before := by
    exact .second (.var (by simpa only [List.getElem?_cons_zero] using congrArg some dispatch.shape))
  have exactGate := site.dispatch_known .beforeArguments unknown dispatch.contract dispatch.row dispatch.found read
  cases answer : dispatch.row.beforeArguments with
  | ok unitValue =>
      cases unitValue
      rw [reason_accepted dispatch.row site.reasonAt .beforeArguments answer] at exactGate
      have identical := (evaluation_deterministic evaluation.sound exactGate).1
      cases identical
  | error diagnostic =>
      rw [reason_rejected dispatch.row site.reasonAt .beforeArguments diagnostic answer] at exactGate
      obtain ⟨same, store⟩ := evaluation_deterministic evaluation.sound exactGate
      obtain ⟨reason, rejected, errorEq⟩ := dispatch.rejected_of_error diagnostic answer
      have tokenEq : token = dispatch.reason reason := by
        cases same
        simp only [CallStageBoundary.Dispatch.reason, errorEq]
      exact ⟨reason, rejected, by simpa only [tokenEq] using dispatch.reason_represents reason, store⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndirectCallBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndirectCallSourceBounds
/-! Original source derivations at the indirect-call boundary. The retained
children keep their own grades, caller and invocation dictionaries, ordered
arguments and every intermediate heap. Closure application keeps the actual
copies of the captures and the parameter allocation. These inversions do not construct a callable's
catalog authority, compiler receipt or body execution meaning. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndirectCallSourceBounds
open Frontend SourceInference
open RecursiveNamedCallBounds

inductive IndirectTraceAt (program : Program) (size : Nat) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (callee : ExpressionId) (arguments : List ExpressionId)
    (metadata : IndirectCallResolution) (requirements : List RequirementId) :
    Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | calleeFault {childSize reason after}
      (child : SourceExecutionSize.ExpressionFaults program childSize context evidence source environment before callee reason after)
      (smaller : childSize < size) :
      IndirectTraceAt program size context evidence source environment before callee arguments metadata requirements (.fault reason) after
  | notCallable {childSize callable after}
      (child : SourceExecutionSize.ExpressionEvaluates program childSize context evidence source environment before callee callable after)
      (invalid : ¬ Dynamic.CallableValue callable) (smaller : childSize < size) :
      IndirectTraceAt program size context evidence source environment before callee arguments metadata requirements (.fault .notCallable) after
  | argumentsFault {calleeSize argumentsSize callable calleeHeap reason after}
      (calleeTrace : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment before callee callable calleeHeap)
      (callableShape : Dynamic.CallableValue callable)
      (argumentsTrace : SourceExecutionSize.ExpressionsFault program argumentsSize context evidence source environment calleeHeap arguments reason after)
      (calleeSmaller : calleeSize < size) (argumentsSmaller : argumentsSize < size) :
      IndirectTraceAt program size context evidence source environment before callee arguments metadata requirements (.fault reason) after
  | sourceArity {calleeSize argumentsSize callable values calleeHeap argumentsHeap}
      (calleeTrace : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment before callee callable calleeHeap)
      (argumentsTrace : SourceExecutionSize.ExpressionsEvaluate program argumentsSize context evidence source environment calleeHeap arguments values argumentsHeap)
      (mismatch : metadata.argumentCount ≠ arguments.length)
      (calleeSmaller : calleeSize < size) (argumentsSmaller : argumentsSize < size) :
      IndirectTraceAt program size context evidence source environment before callee arguments metadata requirements
        (.fault (.argumentArityMismatch metadata.argumentCount arguments.length)) argumentsHeap
  | argumentCoercionFault {calleeSize argumentsSize coercionSize callable values packed calleeHeap argumentsHeap reason after}
      (calleeTrace : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment before callee callable calleeHeap)
      (argumentsTrace : SourceExecutionSize.ExpressionsEvaluate program argumentsSize context evidence source environment calleeHeap arguments values argumentsHeap)
      (arity : arguments.length = metadata.argumentCount) (pack : Dynamic.ValuesPack values packed)
      (coercionTrace : SourceExecutionSize.CoercionPathFaults program coercionSize context evidence argumentsHeap metadata.argumentCoercions packed reason after)
      (calleeSmaller : calleeSize < size) (argumentsSmaller : argumentsSize < size) (coercionSmaller : coercionSize < size) :
      IndirectTraceAt program size context evidence source environment before callee arguments metadata requirements (.fault reason) after
  | applied {calleeSize argumentsSize coercionSize callSize callable values packed coerced appliedArguments
        invocationEvidence calleeHeap argumentsHeap coercedHeap result after}
      (layout : requirements = coercionRequirementIds metadata.argumentCoercions)
      (calleeTrace : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment before callee callable calleeHeap)
      (argumentsTrace : SourceExecutionSize.ExpressionsEvaluate program argumentsSize context evidence source environment calleeHeap arguments values argumentsHeap)
      (packBefore : Dynamic.ValuesPack values packed)
      (coercionTrace : SourceExecutionSize.CoercionPathExecutes program coercionSize context evidence argumentsHeap metadata.argumentCoercions packed coerced coercedHeap)
      (packAfter : Dynamic.ValuesPack appliedArguments coerced)
      (sourceArity : arguments.length = metadata.argumentCount) (appliedArity : appliedArguments.length = metadata.argumentCount)
      (application : SourceExecutionSize.CallableApplies program callSize context evidence invocationEvidence coercedHeap callable appliedArguments result after)
      (calleeSmaller : calleeSize < size) (argumentsSmaller : argumentsSize < size)
      (coercionSmaller : coercionSize < size) (callSmaller : callSize < size) :
      IndirectTraceAt program size context evidence source environment before callee arguments metadata requirements (.value result) after
  | applicationFault {calleeSize argumentsSize coercionSize callSize callable values packed coerced appliedArguments
        invocationEvidence calleeHeap argumentsHeap coercedHeap reason after}
      (calleeTrace : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment before callee callable calleeHeap)
      (argumentsTrace : SourceExecutionSize.ExpressionsEvaluate program argumentsSize context evidence source environment calleeHeap arguments values argumentsHeap)
      (packBefore : Dynamic.ValuesPack values packed)
      (coercionTrace : SourceExecutionSize.CoercionPathExecutes program coercionSize context evidence argumentsHeap metadata.argumentCoercions packed coerced coercedHeap)
      (packAfter : Dynamic.ValuesPack appliedArguments coerced)
      (sourceArity : arguments.length = metadata.argumentCount) (appliedArity : appliedArguments.length = metadata.argumentCount)
      (application : SourceExecutionSize.CallableFaults program callSize context evidence invocationEvidence coercedHeap callable appliedArguments reason after)
      (calleeSmaller : calleeSize < size) (argumentsSmaller : argumentsSize < size)
      (coercionSmaller : coercionSize < size) (callSmaller : callSize < size) :
      IndirectTraceAt program size context evidence source environment before callee arguments metadata requirements (.fault reason) after

/-- The wrapper's original raw child is inverted once. No child is remeasured. -/
theorem indirect_inv_sized
    {program : Program} {size : Nat} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {call callee : ExpressionId} {arguments : List ExpressionId}
    {node : ExpressionNode} {metadata : IndirectCallResolution} {outcome : Dynamic.ExpressionOutcome}
    (found : source.lookupExpression? call = some node)
    (form : node.form = .call callee arguments (.indirect metadata)) (coercions : node.coercions = [])
    (unique : NodeOccurrencesUnique source)
    (original : ExpressionOutcome program size context evidence source environment before call outcome after) :
    IndirectTraceAt program size context evidence source environment before callee arguments metadata node.requirements outcome after := by
  cases original with
  | value evaluated =>
    obtain ⟨_, raw, smaller⟩ := RecursiveNamedExpressionSourceBounds.evaluation_raw_sized unique
      (lookupExpression?_sound found) (by intros; simp [form]) coercions evaluated
    rw [form, coercions] at raw
    cases raw with
    | indirectCall layout first children packed converted unpacked arity applied application =>
      refine .applied (by simpa [coercionRequirementIds] using layout) first children packed converted unpacked arity applied application ?_ ?_ ?_ ?_
      all_goals exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
  | fault failed =>
    obtain ⟨_, raw, smaller⟩ := RecursiveNamedExpressionSourceBounds.fault_raw_sized unique
      (lookupExpression?_sound found) (by intros; simp [form]) coercions failed
    rw [form, coercions] at raw
    cases raw with
    | indirectCallee child =>
      exact .calleeFault child (Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller)
    | indirectNotCallable child invalid =>
      exact .notCallable child invalid (Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller)
    | indirectArguments first callable children =>
      refine .argumentsFault first callable children ?_ ?_
      all_goals exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
    | indirectSourceArity first children mismatch =>
      refine .sourceArity first children mismatch ?_ ?_
      all_goals exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
    | indirectArgumentCoercion first children arity packed failed =>
      refine .argumentCoercionFault first children arity packed failed ?_ ?_ ?_
      all_goals exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
    | indirectApply first children packed converted unpacked arity applied failed =>
      refine .applicationFault first children packed converted unpacked arity applied failed ?_ ?_ ?_ ?_
      all_goals exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller

inductive ClosureCompletion (program : Program) (context : SourceSemantics.Context)
    (caller invocation : Dynamic.EvidenceEnvironment) (before : Dynamic.Heap)
    (function : Dynamic.Closure) (arguments : List Dynamic.Value) :
    Nat → Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | arity (mismatch : function.parameters.length ≠ arguments.length) :
      ClosureCompletion program context caller invocation before function arguments (SourceExecutionSize.stepSize [])
        (.fault (.argumentArityMismatch function.parameters.length arguments.length)) before
  | reached {size bodySize parameterTypes callContext entry copied environment bound outcome after}
      (sameEvidence : invocation = function.evidence) (frame : Dynamic.ClosureFrame program function)
      (parameters : MonoBindersExtend function.source.owner function.context function.parameters parameterTypes callContext)
      (copy : Dynamic.EnvironmentCopies function.source function.captured before entry copied)
      (allocation : Dynamic.BindersAllocate entry copied function.parameters arguments environment bound)
      (body : BodyTrace program bodySize function callContext environment bound outcome after)
      (smaller : bodySize < size) (grade : size = SourceExecutionSize.stepSize [bodySize]) :
      ClosureCompletion program context caller invocation before function arguments size outcome after

/-- The copies of the captures, the full parameter allocation and the original
body child are retained directly from each closure application constructor,
including control escape. -/
theorem closure_completed_sized
    {program : Program} {size : Nat} {context : SourceSemantics.Context}
    {caller invocation : Dynamic.EvidenceEnvironment} {before after : Dynamic.Heap}
    {function : Dynamic.Closure} {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (original : CallOutcome program size context caller invocation before (.closure function) arguments outcome after) :
    ClosureCompletion program context caller invocation before function arguments size outcome after := by
  cases original with
  | value applied =>
    cases applied with
    | closure same frame parameters copy allocation executed returned =>
      cases returned
      exact .reached same frame parameters copy allocation (.returned executed)
        (SourceExecutionSize.child_lt_stepSize (by simp)) rfl
    | closureUnit same frame unit parameters copy allocation executed fellThrough =>
      obtain ⟨_, rfl⟩ := fellThrough
      exact .reached same frame parameters copy allocation (.unit unit executed)
        (SourceExecutionSize.child_lt_stepSize (by simp)) rfl
  | fault failed =>
    cases failed with
    | notCallable invalid => exact False.elim (invalid trivial)
    | closureArity mismatch => exact .arity mismatch
    | closureBody same frame parameters copy allocation failed =>
      exact .reached same frame parameters copy allocation (.fault failed)
        (SourceExecutionSize.child_lt_stepSize (by simp)) rfl
    | closureControlEscape same frame parameters copy allocation executed escaped =>
      exact .reached same frame parameters copy allocation (.escaped executed escaped)
        (SourceExecutionSize.child_lt_stepSize (by simp)) rfl

end Solcore.SourceSemantics.CoreLowering.CallableIndirectCallSourceBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableFaultDiagnosticPreparation
/-! Exact callable diagnostic rows from successful artifact preparation.
The static inventory retains the actual first token lookup and the raw error;
it makes no claim about arbitrary semantic faults or staged rejection. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CallableFaultDiagnosticPreparation
open Core Frontend SourceInference SourceCoreCallableFaultSites

private def selects (row : SourceCoreStageCodebook.Decision) (phase : Phase)
    (error : RuntimeError) (site : Site) : Bool :=
  decide (site.caller = row.caller ∧ site.call = row.call ∧ site.contract = row.entry.id ∧
    site.phase = phase ∧ site.error = error)

/-- The actual issued rows have fresh positive tokens, exact token lookup and
unchanged diagnostic errors. Bounds retain the original allocator offset. -/
structure Inventory (start : Nat) (sites : List Site) : Prop where
  bounds : ∀ site, site ∈ sites → start < site.reason.val ∧ site.reason.val ≤ start + sites.length
  found : ∀ site, site ∈ sites → sites.find? (fun candidate => decide (candidate.reason = site.reason)) = some site
  error : ∀ site, site ∈ sites → site.diagnostic.error = site.error

private theorem Inventory.empty (start : Nat) : Inventory start [] := by
  constructor <;> intro site member <;> cases member

private theorem Inventory.append {start : Nat} {sites : List Site} (before : Inventory start sites)
    {site : Site} (number : site.reason.val = start + 1 + sites.length)
    (error : site.diagnostic.error = site.error) : Inventory start (sites ++ [site]) := by
  have distinct : ∀ candidate, candidate ∈ sites → candidate.reason ≠ site.reason := by
    intro candidate member same
    have bound := (before.bounds candidate member).2
    have numbers := congrArg Fin.val same
    omega
  have absent : sites.find? (fun candidate => decide (candidate.reason = site.reason)) = none := by
    apply List.find?_eq_none.mpr
    intro candidate member
    intro same
    exact distinct candidate member (of_decide_eq_true same)
  constructor
  · intro candidate member
    rcases List.mem_append.mp member with old | fresh
    · have bound := before.bounds candidate old
      simp only [List.length_append, List.length_singleton]
      omega
    · have same := List.mem_singleton.mp fresh
      subst candidate
      simp only [List.length_append, List.length_singleton]
      omega
  · intro candidate member
    rcases List.mem_append.mp member with old | fresh
    · rw [List.find?_append, before.found candidate old]; rfl
    · have same := List.mem_singleton.mp fresh
      subst candidate
      rw [List.find?_append, absent]
      simp
  · intro candidate member
    rcases List.mem_append.mp member with old | fresh
    · exact before.error candidate old
    · exact List.mem_singleton.mp fresh ▸ error

private def answer (row : SourceCoreStageCodebook.Decision) : Phase → Except RuntimeError Unit
  | .beforeArguments => row.beforeArguments
  | .beforeApplication => row.afterArguments

/-- Every actually rejected phase has a real emitted row. Its raw error and
contract identify the same selected artifact decision. -/
def Covered (row : SourceCoreStageCodebook.Decision) (sites : List Site) : Prop :=
  ∀ phase error, answer row phase = .error error →
    ∃ site, site ∈ sites ∧ selects row phase error site = true

private theorem Covered.grows {row : SourceCoreStageCodebook.Decision}
    {before after : List Site} (covered : Covered row before)
    (growth : ∃ suffix, after = before ++ suffix) : Covered row after := by
  obtain ⟨suffix, rfl⟩ := growth
  intro phase error failed
  obtain ⟨site, member, same⟩ := covered phase error failed
  exact ⟨site, List.mem_append_left _ member, same⟩

private theorem bind_ok {α β ε : Type} {value : Except ε α} {next : α → Except ε β} {result : β}
    (accepted : (value >>= next) = .ok result) :
    ∃ middle, value = .ok middle ∧ next middle = .ok result := by
  cases value with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem word_number {number : Nat} {reason : Word}
    (accepted : (match Word.ofNat? number with
      | some value => Except.ok value
      | none => Except.error SourceCoreCallableFaultSites.Error.reasonSpaceExhausted) = .ok reason) :
    reason.val = number := by
  split at accepted
  · rename_i converted
    have same := Except.ok.inj accepted
    subst reason
    unfold Word.ofNat? at converted
    split at converted
    · exact congrArg Fin.val (Option.some.inj converted).symm
    · cases converted
  · cases accepted

private theorem phase_inventory {start : Nat} {row : SourceCoreStageCodebook.Decision}
    {node : ExpressionNode} {sites result : List Site}
    {issue : Nat → Except SourceCoreCallableFaultSites.Error Word}
    (wordEq : ∀ number, issue number = match Word.ofNat? number with
      | some value => Except.ok value | none => Except.error .reasonSpaceExhausted)
    (before : Inventory start sites)
    (ran : forIn ([.beforeArguments, .beforeApplication] : List Phase) sites (fun (phase : Phase) (current : List Site) => do
      let answer : Except RuntimeError Unit := match phase with
        | .beforeArguments => row.beforeArguments | .beforeApplication => row.afterArguments
      match answer with
      | .ok _ => pure (ForInStep.yield current)
      | .error error =>
          let reason ← issue (start + 1 + current.length)
          let diagnostic : SourceCoreFaultSites.Diagnostic :=
            { error, site := .occurrence row.call.occurrence, span := some node.span }
          pure (ForInStep.yield (current ++ [(⟨row.caller, row.call, row.entry.id, phase, error, reason, diagnostic⟩ : Site)]))) = .ok result) :
    Inventory start result ∧ (∃ suffix, result = sites ++ suffix) ∧ Covered row result := by
  have retained := CompatibleMemberCertificates.forIn_preserves ran
    (fun seen current => Inventory start current ∧ (∃ suffix, current = sites ++ suffix) ∧
      (∀ phase, phase ∈ seen → ∀ error, answer row phase = .error error →
        ∃ site, site ∈ current ∧ selects row phase error site = true))
  have final : Inventory start result ∧ (∃ suffix, result = sites ++ suffix) ∧
      (∀ phase, phase ∈ ([.beforeArguments, .beforeApplication] : List Phase) →
        ∀ error, answer row phase = .error error → ∃ site, site ∈ result ∧ selects row phase error site = true) := by
    apply retained
    · exact ⟨before, ⟨[], (List.append_nil _).symm⟩, fun _ member => False.elim (List.not_mem_nil member)⟩
    · intro seen phase remaining current outcome _split previous step
      change (match answer row phase with
        | .ok _ => Except.ok (ForInStep.yield current)
        | .error error => do
            let reason ← issue (start + 1 + current.length)
            pure (ForInStep.yield (current ++ [(⟨row.caller, row.call, row.entry.id, phase, error, reason,
              ⟨error, .occurrence row.call.occurrence, some node.span⟩⟩ : Site)]))) = .ok outcome at step
      split at step
      · rename_i accepted
        refine ⟨current, (Except.ok.inj step).symm, previous.1, previous.2.1, ?_⟩
        intro prior member error failed
        rcases List.mem_append.mp member with old | fresh
        · exact previous.2.2 prior old error failed
        · have same := List.mem_singleton.mp fresh
          subst prior
          change answer row _ = .ok _ at accepted
          rw [accepted] at failed
          cases failed
      · rename_i error failed
        obtain ⟨reason, issued, step⟩ := bind_ok step
        rw [wordEq] at issued
        have number := word_number issued
        let site : Site := ⟨row.caller, row.call, row.entry.id, phase, error, reason,
          ⟨error, .occurrence row.call.occurrence, some node.span⟩⟩
        have inventory := previous.1.append (site := site) number rfl
        obtain ⟨suffix, growth⟩ := previous.2.1
        refine ⟨current ++ [site], (Except.ok.inj step).symm, inventory,
          ⟨suffix ++ [site], by rw [growth, List.append_assoc]⟩, ?_⟩
        intro prior member actualError actualFailed
        rcases List.mem_append.mp member with old | fresh
        · obtain ⟨oldSite, oldMember, oldSame⟩ := previous.2.2 prior old actualError actualFailed
          exact ⟨oldSite, List.mem_append_left _ oldMember, oldSame⟩
        · have same := List.mem_singleton.mp fresh
          subst prior
          change answer row _ = .error error at failed
          have sameError := Except.error.inj (failed.symm.trans actualFailed)
          subst actualError
          exact ⟨site, List.mem_append_right _ (List.mem_singleton_self _), by simp [site, selects]⟩
  refine ⟨final.1, final.2.1, ?_⟩
  intro phase error failed
  exact final.2.2 phase (by cases phase <;> simp) error failed

/-- The original allocator begins above every used base-table token. -/
def offset (base : SourceCoreFaultSites.Table) (minimum : Nat) : Nat :=
  max (((base.reads.map (·.reason.val) ++ base.additional.map (·.1.val) ++
    [base.escapedReason.val]).foldl max 0) + 1) minimum

/-- Finite static facts about the actual successful callable diagnostic factory. -/
structure Receipt (contracts : Table) (base : SourceCoreFaultSites.Table) (minimum : Nat)
    (program : SourceCoreCallableFaultSites.Program) : Prop where
  unknown : program.unknown.val = offset base minimum
  inventory : Inventory (offset base minimum) program.sites
  covered : ∀ row, row ∈ contracts.decisions → Covered row program.sites
  table : program.rootTable = { base with
    additional := base.additional ++ [(program.unknown,
      ⟨.deepSafetyInputsRejected, .declaration base.owner, none⟩)] ++
      program.sites.map (fun site => (site.reason, site.diagnostic)) }

/-- Successful artifact preparation itself proves row coverage and fresh token
lookup. The only traversal is the existing static compiler loop. -/
theorem prepare_receipt {plan : SourceCoreStageCodebook.Plan} {contracts : Table}
    {base : SourceCoreFaultSites.Table} {minimum : Nat} {program : SourceCoreCallableFaultSites.Program}
    (prepared : SourceCoreCallableFaultSites.prepare plan contracts base minimum = .ok program) :
    Receipt contracts base minimum program := by
  unfold SourceCoreCallableFaultSites.prepare at prepared
  obtain ⟨unknown, issued, prepared⟩ := bind_ok prepared
  have unknownNumber : unknown.val = offset base minimum := word_number issued
  obtain ⟨sites, loop, returned⟩ := bind_ok prepared
  have final : Inventory (offset base minimum) sites ∧
      ∀ row, row ∈ contracts.decisions → Covered row sites := by
    apply CompatibleMemberCertificates.forIn_preserves loop
      (fun seen current => Inventory (offset base minimum) current ∧
        ∀ row, row ∈ seen → Covered row current)
    · exact ⟨Inventory.empty _, fun _ member => False.elim (List.not_mem_nil member)⟩
    · intro seen row remaining current outcome _split previous step
      dsimp only at step
      split at step
      · rename_i caller callerFound
        try dsimp only [pure, Except.pure, bind, Except.bind] at step
        split at step
        · rename_i node nodeFound
          try dsimp only [pure, Except.pure, bind, Except.bind] at step
          obtain ⟨updated, phases, returned⟩ := bind_ok step
          have receipt := phase_inventory (start := offset base minimum) (row := row) (node := node)
            (fun _ => rfl) previous.1 phases
          refine ⟨updated, (Except.ok.inj returned).symm, receipt.1, ?_⟩
          intro prior member
          rcases List.mem_append.mp member with old | fresh
          · exact (previous.2 prior old).grows receipt.2.1
          · exact List.mem_singleton.mp fresh ▸ receipt.2.2
        · change (Except.error _ : Except SourceCoreCallableFaultSites.Error _) = .ok outcome at step
          cases step
      · change (Except.error _ : Except SourceCoreCallableFaultSites.Error _) = .ok outcome at step
        cases step
  cases Except.ok.inj returned
  exact ⟨unknownNumber, final.1, final.2, rfl⟩

private theorem foldl_max_initial (values : List Nat) (initial : Nat) : initial ≤ values.foldl max initial := by
  induction values generalizing initial with
  | nil => exact Nat.le_refl _
  | cons head tail ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

private theorem foldl_max_member (values : List Nat) {value : Nat} (member : value ∈ values) (initial : Nat) :
    value ≤ values.foldl max initial := by
  induction values generalizing initial with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact Nat.le_trans (Nat.le_max_right _ _) (foldl_max_initial tail _)
    · exact ih member _

private theorem offset_used {base : SourceCoreFaultSites.Table} {minimum number : Nat}
    (used : number ∈ base.reads.map (·.reason.val) ++ base.additional.map (·.1.val) ++
      [base.escapedReason.val]) : number < offset base minimum := by
  have bound := foldl_max_member _ used 0
  have start := Nat.le_max_left
    ((base.reads.map (·.reason.val) ++ base.additional.map (·.1.val) ++ [base.escapedReason.val]).foldl max 0 + 1) minimum
  unfold offset
  omega

/-- The authentic selected rejection token decodes to its own raw diagnostic
error in the actual extended table. No semantic FaultRep is assumed. -/
theorem Receipt.diagnostic {contracts : Table} {base : SourceCoreFaultSites.Table}
    {minimum : Nat} {program : SourceCoreCallableFaultSites.Program}
    (receipt : Receipt contracts base minimum program)
    {row : SourceCoreStageCodebook.Decision} (member : row ∈ contracts.decisions)
    {phase : Phase} {error : RuntimeError} (failed : answer row phase = .error error) :
    ∃ diagnostic,
      program.rootTable.diagnostic? (program.reasonAt row.caller row.call row.entry.id phase error) = some diagnostic ∧
      diagnostic.error = error := by
  obtain ⟨emitted, emittedMember, emittedMatches⟩ := receipt.covered row member phase error failed
  have covered : (program.sites.find? (selects row phase error)).isSome :=
    List.find?_isSome.mpr ⟨emitted, emittedMember, emittedMatches⟩
  cases selected : program.sites.find? (selects row phase error) with
  | none => simp only [selected, Option.isSome_none, Bool.false_eq_true] at covered
  | some site =>
    have siteMember := List.mem_of_find?_eq_some selected
    have same := of_decide_eq_true (List.find?_some (p := selects row phase error) selected)
    have token : program.reasonAt row.caller row.call row.entry.id phase error = site.reason := by
      simp only [SourceCoreCallableFaultSites.Program.reasonAt]
      change (match program.sites.find? (selects row phase error) with
        | some chosen => chosen.reason | none => program.unknown) = site.reason
      rw [selected]
    have high := (receipt.inventory.bounds site siteMember).1
    have positive : site.reason ≠ Word.zero := by intro zero; have zeroVal := congrArg Fin.val zero; change site.reason.val = 0 at zeroVal; omega
    have escaped : site.reason ≠ base.escapedReason := by
      intro equal
      have before := offset_used (base := base) (minimum := minimum) (number := base.escapedReason.val)
        (List.mem_append_right _ (List.mem_singleton_self _))
      have numbers := congrArg Fin.val equal
      omega
    have baseAbsent : base.additional.find? (fun candidate => decide (candidate.1 = site.reason)) = none := by
      apply List.find?_eq_none.mpr
      intro candidate contained equal
      have before := offset_used (base := base) (minimum := minimum) (number := candidate.1.val)
        (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨candidate, contained, rfl⟩)))
      have numbers := congrArg Fin.val (of_decide_eq_true equal)
      omega
    have unknownDistinct : program.unknown ≠ site.reason := by
      intro equal
      have numbers := congrArg Fin.val equal
      have actual := receipt.unknown
      omega
    have siteFound : (program.sites.map (fun actual => (actual.reason, actual.diagnostic))).find?
        (fun candidate => decide (candidate.1 = site.reason)) = some (site.reason, site.diagnostic) := by
      rw [List.find?_map]
      change (program.sites.find? (fun candidate => decide (candidate.reason = site.reason))).map
        (fun actual => (actual.reason, actual.diagnostic)) = _
      rw [receipt.inventory.found site siteMember]; rfl
    refine ⟨site.diagnostic, ?_, (receipt.inventory.error site siteMember).trans same.2.2.2.2⟩
    rw [token, receipt.table]
    simp only [SourceCoreFaultSites.Table.diagnostic?, positive, escaped, if_false]
    rw [List.find?_append, List.find?_append, baseAbsent]
    simp only [List.find?_cons, decide_eq_false unknownDistinct,
      List.find?_nil, Option.or_none, siteFound, Option.or_some]
    rfl

/-- The real first phase rejection retains its raw stage diagnostic. -/
theorem prepared_before_arguments {plan : SourceCoreStageCodebook.Plan} {contracts : Table}
    {base : SourceCoreFaultSites.Table} {minimum : Nat} {program : SourceCoreCallableFaultSites.Program}
    (prepared : SourceCoreCallableFaultSites.prepare plan contracts base minimum = .ok program)
    {row : SourceCoreStageCodebook.Decision} (member : row ∈ contracts.decisions)
    {error : RuntimeError} (failed : row.beforeArguments = .error error) :
    ∃ diagnostic, program.rootTable.diagnostic?
      (program.reasonAt row.caller row.call row.entry.id .beforeArguments error) = some diagnostic ∧
      diagnostic.error = error :=
  (prepare_receipt prepared).diagnostic member failed

/-- The real second phase rejection retains its raw invocation diagnostic. -/
theorem prepared_after_arguments {plan : SourceCoreStageCodebook.Plan} {contracts : Table}
    {base : SourceCoreFaultSites.Table} {minimum : Nat} {program : SourceCoreCallableFaultSites.Program}
    (prepared : SourceCoreCallableFaultSites.prepare plan contracts base minimum = .ok program)
    {row : SourceCoreStageCodebook.Decision} (member : row ∈ contracts.decisions)
    {error : RuntimeError} (failed : row.afterArguments = .error error) :
    ∃ diagnostic, program.rootTable.diagnostic?
      (program.reasonAt row.caller row.call row.entry.id .beforeApplication error) = some diagnostic ∧
      diagnostic.error = error :=
  (prepare_receipt prepared).diagnostic member failed

/-- The application arity rejection uses the exact same issued phase row. -/
theorem prepared_application_arity {plan : SourceCoreStageCodebook.Plan} {contracts : Table}
    {base : SourceCoreFaultSites.Table} {minimum : Nat} {program : SourceCoreCallableFaultSites.Program}
    (prepared : SourceCoreCallableFaultSites.prepare plan contracts base minimum = .ok program)
    {row : SourceCoreStageCodebook.Decision} (member : row ∈ contracts.decisions)
    (different : row.entry.parameterCount ≠ row.argumentCount) :
    ∃ diagnostic, program.rootTable.diagnostic?
      (program.reasonAt row.caller row.call row.entry.id .beforeApplication
        (.argumentArityMismatch row.entry.parameterCount row.argumentCount)) = some diagnostic ∧
      diagnostic.error = .argumentArityMismatch row.entry.parameterCount row.argumentCount :=
  (prepare_receipt prepared).diagnostic member (SourceCoreStageCodebook.Decision.afterArguments_mismatch row different)

end Solcore.SourceSemantics.CoreLowering.CallableFaultDiagnosticPreparation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableBodyMetadataViews
/-! Correspondence restricted to the actual roots of a callable body.
The source table may contain unrelated nodes and different input types.
The relation preserves input identities and the forms read along real paths;
it does not assert typing or execution equivalence by itself. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableBodyMetadataViews
open Frontend SourceInference CallableLambdaBodyReachability LambdaMetadataViews

structure BodyView (source view : TypedSource) (roots : List NodeId) : Prop where
  owner : source.owner = view.owner
  inputs : source.inputs.map TypedBinder.id = view.inputs.map TypedBinder.id
  expression {id : ExpressionId}
      (reached : Reaches source roots (.expression id) ∨ Reaches view roots (.expression id))
      {node : ExpressionNode} (found : view.lookupExpression? id = some node) :
      ∃ original, source.lookupExpression? id = some original ∧
        original.id = node.id ∧ original.form = node.form
  expression_back {id : ExpressionId}
      (reached : Reaches source roots (.expression id) ∨ Reaches view roots (.expression id))
      {node : ExpressionNode} (found : source.lookupExpression? id = some node) :
      ∃ original, view.lookupExpression? id = some original ∧
        original.id = node.id ∧ original.form = node.form
  statement {id : StatementId}
      (reached : Reaches source roots (.statement id) ∨ Reaches view roots (.statement id)) :
      source.lookupStatement? id = view.lookupStatement? id

theorem BodyView.of_metadata {source view : TypedSource}
    (related : MetadataView source view) (roots : List NodeId) :
    BodyView source view roots where
  owner := related.owner
  inputs := congrArg (List.map TypedBinder.id) related.inputs
  expression _ _ found := related.expression found
  expression_back _ _ found := related.symm.expression found
  statement _ := by
    cases found : source.lookupStatement? _ with
    | none =>
      cases other : view.lookupStatement? _ with
      | none => rfl
      | some node => have := related.statement other; simp only [found] at this; cases this
    | some node => exact (related.symm.statement found).symm

theorem BodyView.refl (source : TypedSource) (roots : List NodeId) :
    BodyView source source roots := BodyView.of_metadata (MetadataView.refl source) roots

theorem BodyView.symm {source view : TypedSource} {roots : List NodeId}
    (related : BodyView source view roots) : BodyView view source roots where
  owner := related.owner.symm
  inputs := related.inputs.symm
  expression reached _ found := related.expression_back reached.symm found
  expression_back reached _ found := related.expression reached.symm found
  statement reached := (related.statement reached.symm).symm

theorem BodyView.reaches {source view : TypedSource} {roots : List NodeId}
    (related : BodyView source view roots) {id : NodeId} (reached : Reaches source roots id) :
    Reaches view roots id := by
  induction reached with
  | root member => exact .root member
  | expression parent found edge ih =>
    obtain ⟨node, selected, _, form⟩ := related.expression_back (.inl parent) found
    exact .expression ih selected (form ▸ edge)
  | statement parent found edge ih =>
    exact .statement ih ((related.statement (.inl parent)).symm.trans found) edge

theorem BodyView.trans {source middle view : TypedSource} {roots : List NodeId}
    (first : BodyView source middle roots) (second : BodyView middle view roots) :
    BodyView source view roots where
  owner := first.owner.trans second.owner
  inputs := first.inputs.trans second.inputs
  expression reached _ found := by
    have atMiddle : Reaches middle roots _ :=
      reached.elim first.reaches second.symm.reaches
    obtain ⟨between, foundMiddle, sameId, sameForm⟩ := second.expression (.inl atMiddle) found
    obtain ⟨original, selected, originalId, originalForm⟩ :=
      first.expression (.inr atMiddle) foundMiddle
    exact ⟨original, selected, originalId.trans sameId, originalForm.trans sameForm⟩
  expression_back reached _ found := by
    have atMiddle : Reaches middle roots _ :=
      reached.elim first.reaches second.symm.reaches
    obtain ⟨between, foundMiddle, sameId, sameForm⟩ :=
      first.expression_back (.inr atMiddle) found
    obtain ⟨original, selected, originalId, originalForm⟩ :=
      second.expression_back (.inl atMiddle) foundMiddle
    exact ⟨original, selected, originalId.trans sameId, originalForm.trans sameForm⟩
  statement reached := by
    have atMiddle : Reaches middle roots _ :=
      reached.elim first.reaches second.symm.reaches
    exact (first.statement (.inr atMiddle)).trans (second.statement (.inl atMiddle))

private theorem reaches_from_roots {source : TypedSource} {roots children : List NodeId}
    (parents : ∀ id ∈ children, Reaches source roots id)
    {id : NodeId} (reached : Reaches source children id) : Reaches source roots id := by
  induction reached with
  | root member => exact parents _ member
  | expression _ found edge ih => exact .expression ih found edge
  | statement _ found edge ih => exact .statement ih found edge

/-- A compiler's actual child roots inherit the same correspondence. -/
theorem BodyView.restrict {source view : TypedSource} {roots children : List NodeId}
    (related : BodyView source view roots)
    (parents : ∀ id ∈ children, Reaches source roots id) :
    BodyView source view children where
  owner := related.owner
  inputs := related.inputs
  expression reached _ found := related.expression
    (reached.elim (fun path => .inl (reaches_from_roots parents path))
      (fun path => .inr (reaches_from_roots (fun id member => related.reaches (parents id member)) path)))
    found
  expression_back reached _ found := related.expression_back
    (reached.elim (fun path => .inl (reaches_from_roots parents path))
      (fun path => .inr (reaches_from_roots (fun id member => related.reaches (parents id member)) path)))
    found
  statement reached := related.statement
    (reached.elim (fun path => .inl (reaches_from_roots parents path))
      (fun path => .inr (reaches_from_roots (fun id member => related.reaches (parents id member)) path)))

/-- The initial root comes from the lambda creation occurrence and its actual
body IDs; later expression and statement readers use `reaches`. -/
def lambdaRoots (id : ExpressionId) (body : List StatementId) : List NodeId :=
  .expression id :: body.map NodeId.statement

end Solcore.SourceSemantics.CoreLowering.CallableBodyMetadataViews
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableBodyGraphDescendants
/-! Canonical callable-body reference paths give proper descendants of the
actual parent of the body roots. Every step uses the same source lookup. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableLambdaBodyReachability
open Frontend SourceInference TypeSystem

private theorem expression_child {source : TypedSource} {id : ExpressionId}
    {node : ExpressionNode} (found : source.lookupExpression? id = some node)
    {child : NodeId} (edge : child ∈ node.form.references) :
    DirectChild source (.expression id) child := by
  have contained := lookupExpression?_sound found
  exact ⟨.expression node,
    ⟨contained.1, congrArg NodeId.expression contained.2⟩, edge⟩

private theorem statement_child {source : TypedSource} {id : StatementId}
    {node : StatementNode} (found : source.lookupStatement? id = some node)
    {child : NodeId} (edge : child ∈ node.form.references) :
    DirectChild source (.statement id) child := by
  have contained := lookupStatement?_sound found
  exact ⟨.statement node,
    ⟨contained.1, congrArg NodeId.statement contained.2⟩, edge⟩

/-- Body roots are actual children, so even a root case yields a nonempty
path from the enclosing occurrence. Subsequent steps retain every canonical
reference, including references inside nested initializers. -/
theorem Reaches.descends_of_root_edges {source : TypedSource}
    {roots : List NodeId} {root node : NodeId}
    (path : Reaches source roots node)
    (rootEdges : ∀ child ∈ roots, DirectChild source root child) :
    Descends source root node := by
  induction path with
  | root member => exact .direct (rootEdges _ member)
  | expression _ found edge ih =>
    exact ih.trans (.direct (expression_child found edge))
  | statement _ found edge ih =>
    exact ih.trans (.direct (statement_child found edge))

/-- The exact lambda lookup supplies the body-root edges without a separate
graph-closure premise. The result concerns its actual initializer occurrence. -/
theorem Reaches.descends_from_lambda {source : TypedSource}
    {initializer : ExpressionId} {lambda : ExpressionNode}
    {parameters : List TypedBinder} {result : Ty} {body : List StatementId}
    (found : source.lookupExpression? initializer = some lambda)
    (form : lambda.form = .lambda parameters result body)
    {node : NodeId} (path : Reaches source (body.map NodeId.statement) node) :
    Descends source (.expression initializer) node := by
  apply path.descends_of_root_edges
  intro child member
  apply expression_child found
  simpa only [form, ExpressionForm.references] using member

end Solcore.SourceSemantics.CoreLowering.CallableLambdaBodyReachability
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableBodyViewSubstitution
/-! Substitution preserves actual occurrence paths. A reached-body relation
therefore transports without comparing unrelated source-table entries. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableBodyMetadataViews
open Frontend SourceInference TypeSystem CallableLambdaBodyReachability

private theorem lookupNode_apply (source : TypedSource) (substitution : Substitution)
    (id : OccurrenceId) :
    (source.applySubstitution substitution).lookupNode? id =
      (source.lookupNode? id).map (Node.applySubstitution substitution) := by
  simp only [TypedSource.lookupNode?, TypedSource.applySubstitution, List.find?_map]
  congr 2
  funext candidate
  simp only [Function.comp_apply, Node.occurrenceId_applySubstitution]

theorem lookupExpression_apply (source : TypedSource) (substitution : Substitution)
    (id : ExpressionId) :
    (source.applySubstitution substitution).lookupExpression? id =
      (source.lookupExpression? id).map (ExpressionNode.applySubstitution substitution) := by
  unfold TypedSource.lookupExpression?
  rw [lookupNode_apply]
  cases source.lookupNode? id.occurrence with
  | none => rfl
  | some node => cases node <;> rfl

theorem lookupStatement_apply (source : TypedSource) (substitution : Substitution)
    (id : StatementId) :
    (source.applySubstitution substitution).lookupStatement? id =
      (source.lookupStatement? id).map (StatementNode.applySubstitution substitution) := by
  unfold TypedSource.lookupStatement?
  rw [lookupNode_apply]
  cases source.lookupNode? id.occurrence with
  | none => rfl
  | some node => cases node <;> rfl

theorem reaches_substitution {source : TypedSource} {roots : List NodeId}
    (substitution : Substitution) {id : NodeId} :
    Reaches (source.applySubstitution substitution) roots id ↔ Reaches source roots id := by
  constructor
  · intro reached
    induction reached with
    | root member => exact .root member
    | expression parent found edge ih =>
      rw [lookupExpression_apply] at found
      obtain ⟨node, actual, rfl⟩ := Option.map_eq_some_iff.mp found
      exact .expression ih actual (by simpa only [ExpressionNode.applySubstitution,
        ExpressionForm.applySubstitution_references] using edge)
    | statement parent found edge ih =>
      rw [lookupStatement_apply] at found
      obtain ⟨node, actual, rfl⟩ := Option.map_eq_some_iff.mp found
      exact .statement ih actual (by simpa only [StatementNode.applySubstitution,
        StatementForm.applySubstitution_references] using edge)
  · intro reached
    induction reached with
    | root member => exact .root member
    | expression parent found edge ih =>
      exact .expression ih (by rw [lookupExpression_apply, found]; rfl)
        (by simpa only [ExpressionNode.applySubstitution, ExpressionForm.applySubstitution_references] using edge)
    | statement parent found edge ih =>
      exact .statement ih (by rw [lookupStatement_apply, found]; rfl)
        (by simpa only [StatementNode.applySubstitution, StatementForm.applySubstitution_references] using edge)

/-- The relation follows real paths on either side and preserves only the
metadata that the body readers consume. -/
theorem BodyView.applySubstitution {source view : TypedSource} {roots : List NodeId}
    (related : BodyView source view roots) (substitution : Substitution) :
    BodyView (source.applySubstitution substitution) (view.applySubstitution substitution) roots where
  owner := related.owner
  inputs := by simpa only [TypedSource.applySubstitution_inputIds] using related.inputs
  expression reached _ found := by
    have originalReached : Reaches source roots _ ∨ Reaches view roots _ :=
      reached.imp (reaches_substitution substitution).mp (reaches_substitution substitution).mp
    rw [lookupExpression_apply] at found
    obtain ⟨node, actual, rfl⟩ := Option.map_eq_some_iff.mp found
    obtain ⟨old, selected, sameId, sameForm⟩ := related.expression originalReached actual
    refine ⟨old.applySubstitution substitution, ?_, sameId, ?_⟩
    · rw [lookupExpression_apply, selected]; rfl
    · exact congrArg (ExpressionForm.applySubstitution substitution) sameForm
  expression_back reached _ found := by
    have originalReached : Reaches source roots _ ∨ Reaches view roots _ :=
      reached.imp (reaches_substitution substitution).mp (reaches_substitution substitution).mp
    rw [lookupExpression_apply] at found
    obtain ⟨node, actual, rfl⟩ := Option.map_eq_some_iff.mp found
    obtain ⟨old, selected, sameId, sameForm⟩ := related.expression_back originalReached actual
    refine ⟨old.applySubstitution substitution, ?_, sameId, ?_⟩
    · rw [lookupExpression_apply, selected]; rfl
    · exact congrArg (ExpressionForm.applySubstitution substitution) sameForm
  statement reached := by
    rw [lookupStatement_apply, lookupStatement_apply]
    exact congrArg (Option.map (StatementNode.applySubstitution substitution))
      (related.statement (reached.imp (reaches_substitution substitution).mp (reaches_substitution substitution).mp))

end Solcore.SourceSemantics.CoreLowering.CallableBodyMetadataViews
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableRuntimeNamedBodyFamily
/-! The named family closes actual callee states through the shared measured
body fold. Profiles and gate receipts are obtained only at real parameter
entries; expression children receive strictly smaller actual body meanings. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableRuntimeNamedBodyFamily
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableAncestryPairedLookup RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
universe u v
variable (runtime : Bool) {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {expressionSyntax : Header prepared values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  {faults : FunctionCalls.FaultRep}
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (conditions : ∀ header, BodyCondition (headers := headers) (locations := locations)
    (capturePrefix := capturePrefix) functions registry header)
  (conditionGate : Header prepared values ambient.definitions program → Location → CallableIndexedHistory.NativeFrame → Prop)
  (producers : ∀ header, header ∈ headers → ProtectedStateTransition.MarkedAllocation.Producer protocol header.layouts
    prepared.layout.frame (CompatibleAmbientHeap.payloadModel values.checked registry functions))
  (acquire : ∀ header (member : header ∈ headers) location native, conditionGate header location native →
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt (producers header member).toOrdinary location native)
  (stateTransport : ProtectedStateTransition.AdministrativeTransport protocol)
  (stateBindings : ProtectedStateTransition.Bindings protocol)
  (certificates : Header prepared values ambient.definitions program → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
  (profileProvider : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      (entry : BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost) →
      conditions header entry →
      MatchProfileWith (fun context => RecursiveNamedCatalogMutualMeaning.ContextFor runtime header.solved context header.function.evidence)
        (certificates header) diagnosticPolicy header (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)
  (gateOf : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      (entry : BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost) →
      conditions header entry → conditionGate header frameLocation current)

include extension faithful observations escaped producers acquire stateTransport stateBindings profileProvider gateOf in
/-- Source traces keep their original grade and exact reached pool. No body meaning is an external premise. -/
theorem preserves_at
    (expressionMeaning : ∀ header, header ∈ headers → ∀ context,
      RecursiveNamedCatalogMutualMeaning.ContextFor runtime header.solved context header.function.evidence →
      ∀ budget child, child ≤ budget →
      (∀ callee, callee ∈ headers → RecursiveNamedBoundedContracts.Below budget
        (RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
          (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
          functions registry callee faults protocol (conditions callee))) →
      ProtectedStateTransition.PreservesAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context header.function.evidence header.function.source (certificates header context) faults child)
    (size : Nat) : ∀ header, header ∈ headers →
      RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
        (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
        functions registry header faults protocol (conditions header) size := by
  let Index := Σ header : {header // header ∈ headers}, Σ administrative : Core.Context,
    MatchProfileWith (fun context => RecursiveNamedCatalogMutualMeaning.ContextFor runtime header.val.solved context header.val.function.evidence)
      (certificates header.val) diagnosticPolicy header.val (expressionSyntax header.val)
      (SourceCoreCompatibleCatalog.packTypes (header.val.bindings.map Prod.snd) :: administrative) registry faults
  let origins : Index → CallableRuntimeBodyOrigins.StaticOrigin values ambient registry faults := fun index =>
    CallableRuntimeBodyStaticOrigins.named runtime index.2.2 (escaped index.1.val index.1.property)
  have bodies := CallableRuntimeBodyMutualMeaning.Stateful.preserves_at origins functions extension program faithful observations
    protocol (fun index => conditionGate index.1.val) (fun index => producers index.1.val index.1.property)
    (fun index => acquire index.1.val index.1.property) stateTransport stateBindings
    (by
      intro index context valid budget child within below
      rcases index with ⟨⟨header, member⟩, administrative, profile⟩
      apply expressionMeaning header member context valid budget child within
      intro callee calleeMember smaller strict arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry initial outcome after aligned trace
      let actualProfile := profileProvider callee calleeMember entry aligned
      let target : Index := ⟨⟨callee, calleeMember⟩, administrative, actualProfile⟩
      have meaning := below target smaller strict
      let actualEntry := CallableRuntimeBodyStaticOrigins.named_entry protocol (conditionGate callee)
        runtime actualProfile (escaped callee calleeMember) entry initial (gateOf callee calleeMember entry aligned)
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds, frame, metadata, _, transition⟩ :=
        meaning actualEntry trace
      exact ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds, frame, metadata, transition⟩) size
  intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry initial outcome after aligned trace
  let profile := profileProvider header member entry aligned
  let index : Index := ⟨⟨header, member⟩, administrative, profile⟩
  let actualEntry := CallableRuntimeBodyStaticOrigins.named_entry protocol (conditionGate header)
    runtime profile (escaped header member) entry initial (gateOf header member entry aligned)
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds, frame, metadata, _, transition⟩ :=
    bodies index actualEntry trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds, frame, metadata, transition⟩

include extension faithful observations escaped producers acquire stateTransport stateBindings profileProvider gateOf functionTypes in
/-- Native completions return independent source grades and the actual body post. No body meaning is an external premise. -/
theorem reflects_at
    (expressionMeaning : ∀ header, header ∈ headers → ∀ context,
      RecursiveNamedCatalogMutualMeaning.ContextFor runtime header.solved context header.function.evidence →
      ∀ budget child, child ≤ budget →
      (∀ callee, callee ∈ headers → RecursiveNamedBoundedContracts.Below budget
        (RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
          (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
          functions registry callee faults protocol (conditions callee))) →
      ProtectedStateTransition.ReflectsAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context header.function.evidence header.function.source (certificates header context) faults child)
    (size : Nat) : ∀ header, header ∈ headers →
      RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
        (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
        functions registry header faults protocol (conditions header) size := by
  let Index := Σ header : {header // header ∈ headers}, Σ administrative : Core.Context,
    MatchProfileWith (fun context => RecursiveNamedCatalogMutualMeaning.ContextFor runtime header.val.solved context header.val.function.evidence)
      (certificates header.val) diagnosticPolicy header.val (expressionSyntax header.val)
      (SourceCoreCompatibleCatalog.packTypes (header.val.bindings.map Prod.snd) :: administrative) registry faults
  let origins : Index → CallableRuntimeBodyOrigins.StaticOrigin values ambient registry faults := fun index =>
    CallableRuntimeBodyStaticOrigins.named runtime index.2.2 (escaped index.1.val index.1.property)
  have bodies := CallableRuntimeBodyMutualMeaning.Stateful.reflects_at origins functions extension program faithful observations functionTypes
    protocol (fun index => conditionGate index.1.val) (fun index => producers index.1.val index.1.property)
    (fun index => acquire index.1.val index.1.property) stateTransport stateBindings
    (by
      intro index context valid budget child within below
      rcases index with ⟨⟨header, member⟩, administrative, profile⟩
      apply expressionMeaning header member context valid budget child within
      intro callee calleeMember smaller strict arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry initial value finalStore aligned completed
      let actualProfile := profileProvider callee calleeMember entry aligned
      let target : Index := ⟨⟨callee, calleeMember⟩, administrative, actualProfile⟩
      have meaning := below target smaller strict
      let actualEntry := CallableRuntimeBodyStaticOrigins.named_entry protocol (conditionGate callee)
        runtime actualProfile (escaped callee calleeMember) entry initial (gateOf callee calleeMember entry aligned)
      obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds, frame, metadata, _, transition⟩ :=
        meaning actualEntry completed
      exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds, frame, metadata, transition⟩) size
  intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry initial value finalStore aligned completed
  let profile := profileProvider header member entry aligned
  let index : Index := ⟨⟨header, member⟩, administrative, profile⟩
  let actualEntry := CallableRuntimeBodyStaticOrigins.named_entry protocol (conditionGate header)
    runtime profile (escaped header member) entry initial (gateOf header member entry aligned)
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds, frame, metadata, _, transition⟩ :=
    bodies index actualEntry completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds, frame, metadata, transition⟩

end Solcore.SourceSemantics.CoreLowering.CallableRuntimeNamedBodyFamily
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndirectCallStageBounds
/-! An indirect stage boundary carrying the sizes of its existing dynamic
premises. Static guards keep the same contract and source metadata. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndirectCallStageBounds
open Frontend Frontend.SourceInference Staging.CallBoundary
open SourceExecutionSize (stepSize child_lt_stepSize)

inductive ExecutesAt (program : Program) (frame : Frame) : Nat →
    Context → Dynamic.EvidenceEnvironment → TypedSource → Dynamic.Environment → Dynamic.Heap →
      ExpressionId → ExpressionId → List ExpressionId → IndirectCallResolution → Outcome → Dynamic.Heap → Prop where
  | calleeFault {calleeSize : Nat}
      {context evidence source environment before after call callee arguments metadata reason}
      (fault : SourceExecutionSize.ExpressionFaults program calleeSize context evidence source environment before callee reason after) :
      ExecutesAt program frame (stepSize [calleeSize]) context evidence source environment before call callee arguments metadata (.semanticFault reason) after
  | notCallable {calleeSize : Nat}
      {context evidence source environment before after call callee arguments metadata callable}
      (evaluated : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment before callee callable after)
      (invalid : ¬ Dynamic.CallableValue callable) :
      ExecutesAt program frame (stepSize [calleeSize]) context evidence source environment before call callee arguments metadata (.semanticFault .notCallable) after
  | stageRejected {calleeSize : Nat}
      {context evidence source environment before after call callee arguments metadata callable reason}
      (evaluated : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment before callee callable after)
      (rejected : GuardRejects frame call arguments callable reason) :
      ExecutesAt program frame (stepSize [calleeSize]) context evidence source environment before call callee arguments metadata (.stageFault reason) after
  | argumentsFault {calleeSize argumentsSize : Nat}
      {context evidence source environment before calleeHeap after call callee arguments metadata callable reason}
      (calleeEvaluation : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment before callee callable calleeHeap)
      (accepted : GuardAccepts frame call arguments callable)
      (fault : SourceExecutionSize.ExpressionsFault program argumentsSize context evidence source environment calleeHeap arguments reason after) :
      ExecutesAt program frame (stepSize [calleeSize, argumentsSize]) context evidence source environment before call callee arguments metadata (.semanticFault reason) after
  | sourceArity {calleeSize argumentsSize : Nat}
      {context evidence source environment before calleeHeap argumentsHeap call callee arguments metadata callable values}
      (calleeEvaluation : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment before callee callable calleeHeap)
      (accepted : GuardAccepts frame call arguments callable)
      (argumentsEvaluation : SourceExecutionSize.ExpressionsEvaluate program argumentsSize context evidence source environment calleeHeap arguments values argumentsHeap)
      (mismatch : metadata.argumentCount ≠ arguments.length) :
      ExecutesAt program frame (stepSize [calleeSize, argumentsSize]) context evidence source environment before call callee arguments metadata
        (.semanticFault (.argumentArityMismatch metadata.argumentCount arguments.length)) argumentsHeap
  | argumentCoercionFault {calleeSize argumentsSize coercionsSize : Nat}
      {context evidence source environment before calleeHeap argumentsHeap after call callee arguments metadata
        callable values packed reason}
      (calleeEvaluation : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment before callee callable calleeHeap)
      (accepted : GuardAccepts frame call arguments callable)
      (argumentsEvaluation : SourceExecutionSize.ExpressionsEvaluate program argumentsSize context evidence source environment calleeHeap arguments values argumentsHeap)
      (arity : arguments.length = metadata.argumentCount)
      (pack : Dynamic.ValuesPack values packed)
      (fault : SourceExecutionSize.CoercionPathFaults program coercionsSize context evidence argumentsHeap metadata.argumentCoercions packed reason after) :
      ExecutesAt program frame (stepSize [calleeSize, argumentsSize, coercionsSize]) context evidence source environment before call callee arguments metadata (.semanticFault reason) after
  | applied {calleeSize argumentsSize coercionsSize applicationSize : Nat}
      {context evidence source environment before calleeHeap argumentsHeap coercedHeap after call callee arguments metadata
        callable values packed coerced appliedArguments result invocationEvidence}
      (calleeEvaluation : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment before callee callable calleeHeap)
      (accepted : GuardAccepts frame call arguments callable)
      (argumentsEvaluation : SourceExecutionSize.ExpressionsEvaluate program argumentsSize context evidence source environment calleeHeap arguments values argumentsHeap)
      (packBefore : Dynamic.ValuesPack values packed)
      (coercions : SourceExecutionSize.CoercionPathExecutes program coercionsSize context evidence argumentsHeap metadata.argumentCoercions packed coerced coercedHeap)
      (packAfter : Dynamic.ValuesPack appliedArguments coerced)
      (sourceArity : arguments.length = metadata.argumentCount)
      (appliedArity : appliedArguments.length = metadata.argumentCount)
      (application : SourceExecutionSize.CallableApplies program applicationSize context evidence invocationEvidence coercedHeap callable appliedArguments result after) :
      ExecutesAt program frame (stepSize [calleeSize, argumentsSize, coercionsSize, applicationSize]) context evidence source environment before call callee arguments metadata (.value result) after
  | applicationFault {calleeSize argumentsSize coercionsSize applicationSize : Nat}
      {context evidence source environment before calleeHeap argumentsHeap coercedHeap after call callee arguments metadata
        callable values packed coerced appliedArguments reason invocationEvidence}
      (calleeEvaluation : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment before callee callable calleeHeap)
      (accepted : GuardAccepts frame call arguments callable)
      (argumentsEvaluation : SourceExecutionSize.ExpressionsEvaluate program argumentsSize context evidence source environment calleeHeap arguments values argumentsHeap)
      (packBefore : Dynamic.ValuesPack values packed)
      (coercions : SourceExecutionSize.CoercionPathExecutes program coercionsSize context evidence argumentsHeap metadata.argumentCoercions packed coerced coercedHeap)
      (packAfter : Dynamic.ValuesPack appliedArguments coerced)
      (sourceArity : arguments.length = metadata.argumentCount)
      (appliedArity : appliedArguments.length = metadata.argumentCount)
      (application : SourceExecutionSize.CallableFaults program applicationSize context evidence invocationEvidence coercedHeap callable appliedArguments reason after) :
      ExecutesAt program frame (stepSize [calleeSize, argumentsSize, coercionsSize, applicationSize]) context evidence source environment before call callee arguments metadata (.semanticFault reason) after

namespace ExecutesAt

variable {program : Program} {frame : Frame} {size : Nat} {context : Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {call callee : ExpressionId} {arguments : List ExpressionId}
  {metadata : IndirectCallResolution} {outcome : Outcome}

/-- Retain the original boundary and all its intermediate heaps. -/
theorem sound
    (execution : ExecutesAt program frame size context evidence source environment before
      call callee arguments metadata outcome after) :
    Executes program frame context evidence source environment before
      call callee arguments metadata outcome after := by
  cases execution with
  | calleeFault fault => exact .calleeFault fault.sound
  | notCallable evaluated invalid => exact .notCallable evaluated.sound invalid
  | stageRejected evaluated rejected => exact .stageRejected evaluated.sound rejected
  | argumentsFault evaluated accepted fault =>
    exact .argumentsFault evaluated.sound accepted fault.sound
  | sourceArity evaluated accepted arguments mismatch =>
    exact .sourceArity evaluated.sound accepted arguments.sound mismatch
  | argumentCoercionFault evaluated accepted arguments arity packed fault =>
    exact .argumentCoercionFault evaluated.sound accepted arguments.sound arity packed fault.sound
  | applied evaluated accepted arguments packed converted unpacked arity applied application =>
    exact .applied evaluated.sound accepted arguments.sound packed converted.sound unpacked
      arity applied application.sound
  | applicationFault evaluated accepted arguments packed converted unpacked arity applied fault =>
    exact .applicationFault evaluated.sound accepted arguments.sound packed converted.sound unpacked
      arity applied fault.sound

/-- Each immediate dynamic premise has a smaller size than this boundary. -/
theorem children_below
    (execution : ExecutesAt program frame size context evidence source environment before
      call callee arguments metadata outcome after) :
    ∃ children : List Nat, size = stepSize children ∧ ∀ child ∈ children, child < size := by
  cases execution <;> exact ⟨_, rfl, fun _ member => child_lt_stepSize member⟩

/-- Rejection keeps the original callee size and its entire final heap. -/
theorem stageFault_inv {reason : Staging.CallGuard.Fault}
    (execution : ExecutesAt program frame size context evidence source environment before
      call callee arguments metadata (.stageFault reason) after) :
    ∃ calleeSize callable, size = stepSize [calleeSize] ∧ calleeSize < size ∧
      SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment
        before callee callable after ∧ GuardRejects frame call arguments callable reason := by
  cases execution with
  | stageRejected evaluated rejected =>
    exact ⟨_, _, rfl, child_lt_stepSize (by simp), evaluated, rejected⟩

/-- The same dynamic premises construct the plain form result at this size. -/
theorem value_plain_sized {result : Dynamic.Value} {requirements : List RequirementId}
    {coercions : List CoercionStep}
    (execution : ExecutesAt program frame size context evidence source environment before
      call callee arguments metadata (.value result) after)
    (layout : requirements = coercionRequirementIds metadata.argumentCoercions ++
      coercionRequirementIds coercions) :
    SourceExecutionSize.ExpressionFormEvaluates program size context evidence source environment before
      (.call callee arguments (.indirect metadata)) requirements coercions result after := by
  cases execution with
  | applied evaluated _ arguments packed converted unpacked arity applied application =>
    exact .indirectCall layout evaluated arguments packed converted unpacked arity applied application

/-- The same failing premise constructs the plain form fault at this size. -/
theorem semanticFault_plain_sized {reason : Dynamic.SemanticFault}
    (execution : ExecutesAt program frame size context evidence source environment before
      call callee arguments metadata (.semanticFault reason) after)
    (requirements : List RequirementId) (coercions : List CoercionStep) :
    SourceExecutionSize.ExpressionFormFaults program size context evidence source environment before
      (.call callee arguments (.indirect metadata)) requirements coercions reason after := by
  cases execution with
  | calleeFault fault => exact .indirectCallee fault
  | notCallable evaluated invalid => exact .indirectNotCallable evaluated invalid
  | argumentsFault evaluated accepted fault => exact .indirectArguments evaluated accepted.callable fault
  | sourceArity evaluated _ arguments mismatch => exact .indirectSourceArity evaluated arguments mismatch
  | argumentCoercionFault evaluated _ arguments arity packed fault =>
    exact .indirectArgumentCoercion evaluated arguments arity packed fault
  | applicationFault evaluated _ arguments packed converted unpacked arity applied fault =>
    exact .indirectApply evaluated arguments packed converted unpacked arity applied fault

end ExecutesAt
end Solcore.SourceSemantics.CoreLowering.CallableIndirectCallStageBounds
end
