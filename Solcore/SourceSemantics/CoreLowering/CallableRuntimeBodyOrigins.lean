import Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyKernel

/-! An origin retains an actual static body and its protected entry condition.
Named, lambda, and method provenance stays in the higher adapters. No execution
law is stored here. A reached entry supplies the original environments, heap,
frame, and native code context to the shared body kernel. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyOrigins
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof

structure Origin (values : SourceCoreCompatibleValues.Context)
    (ambient : AmbientDefinitions values.checked.catalog.definitions)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) where
  layouts : SourceCoreAllocationLayouts.Prepared
  owner : SourceSpecialization.SpecializationKey
  active : TypeSystem.Substitution
  frameLayout : SourceCoreCallableIndexedFrames.Layout
  globals : Nat
  onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error
  function : Dynamic.Closure
  expressionSyntax : ExpressionId → Prop
  certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate
  validity : SourceSemantics.Context → Prop
  diagnosticPolicy : AssignmentDiagnosticPolicy
  administrative : Core.Context
  context : SourceSemantics.Context
  scope : SourceCoreLocalCell.Scope
  output : Ty
  code : Expr
  fellThrough : Word
  escaped : Word
  solved : List SolvedRequirement
  protectedEntry : ProtectedExpressionMeaning.Entry
  body : CallableRuntimeBodyKernel.BodyFor layouts owner active frameLayout globals onError values function
    expressionSyntax certificates validity diagnosticPolicy ambient administrative context scope output code
    fellThrough escaped registry faults
  definitions : layouts.definitions = ambient.definitions
  registered : frameLayout.Registered ambient.definitions
  escapedFault : faults .controlEscapedFunction escaped
  transport : ProtectedExpressionMeaning.Transport protectedEntry
  binders : ProtectedExpressionMeaning.Binds protectedEntry
  extend : ∀ {context next binder}, validity context → BinderExtends function.source.owner context binder next → validity next
  runtimeOf : ∀ {context}, validity context → CompatibleRuntimeContextValidity.Valid solved context function.evidence

variable {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- All fields describe this reached state. They confer no new source origin. -/
structure Entry (origin : Origin values ambient registry faults)
    (functions : FunctionModel values.checked.catalog ambient) where
  mapping : LocationMap
  world : StoreTyping
  environment : Dynamic.Environment
  canonical : Environment
  actual : Environment
  heap : Dynamic.Heap
  store : Store
  embedding : Renaming
  actualContext : Core.Context
  frameLocation : Location
  native : CallableIndexedHistory.NativeFrame
  environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
    mapping world origin.administrative origin.scope environment canonical ambient.definitions
  heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store
  locals : Dynamic.EnvironmentAgrees heap origin.context.locals environment
  lookups : EnvironmentsAgree embedding canonical actual
  actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions
  reference : canonical[origin.scope.length + 1 + origin.globals]? = some (.cellRef origin.frameLayout.type frameLocation)
  read : store.read? frameLocation = some (SourceCoreCallableIndexedFrames.encode origin.frameLayout native)
  unmapped : frameLocation ∉ mapping
  installed : origin.protectedEntry origin.scope mapping world heap store canonical

variable (functions : FunctionModel values.checked.catalog ambient) (program : Program)
  (origin : Origin values ambient registry faults)

/-- The source body grade is the original grade. All reached state is retained. -/
def PreservesAt (size : Nat) : Prop :=
  ∀ (entry : Entry origin functions) {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap},
    RecursiveNamedCallBounds.BodyTrace program size origin.function origin.context entry.environment entry.heap outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates entry.actual entry.store (origin.code.rename entry.embedding) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld origin.function.resultType origin.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld origin.administrative program
        origin.function origin.context origin.scope entry.environment entry.heap after outcome ∧
      origin.protectedEntry origin.scope finalMap finalWorld after finalStore entry.canonical

/-- Native completion supplies its own grade; the source grade is an output. -/
def ReflectsAt (size : Nat) : Prop :=
  ∀ (entry : Entry origin functions) {value : Value} {finalStore : Store},
    EvaluationSize size entry.actual entry.store (origin.code.rename entry.embedding) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize origin.function origin.context entry.environment entry.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld origin.function.resultType origin.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld origin.administrative program
        origin.function origin.context origin.scope entry.environment entry.heap after outcome ∧
      origin.protectedEntry origin.scope finalMap finalWorld after finalStore entry.canonical

/-- Source/native origin metadata and static support, with no legacy entry law. -/
structure StaticOrigin (values : SourceCoreCompatibleValues.Context)
    (ambient : AmbientDefinitions values.checked.catalog.definitions)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) where
  layouts : SourceCoreAllocationLayouts.Prepared
  owner : SourceSpecialization.SpecializationKey
  active : TypeSystem.Substitution
  frameLayout : SourceCoreCallableIndexedFrames.Layout
  globals : Nat
  onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error
  function : Dynamic.Closure
  expressionSyntax : ExpressionId → Prop
  certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate
  validity : SourceSemantics.Context → Prop
  diagnosticPolicy : AssignmentDiagnosticPolicy
  administrative : Core.Context
  context : SourceSemantics.Context
  scope : SourceCoreLocalCell.Scope
  output : Ty
  code : Expr
  fellThrough : Word
  escaped : Word
  solved : List SolvedRequirement
  body : CallableRuntimeBodyKernel.BodyFor layouts owner active frameLayout globals onError values function
    expressionSyntax certificates validity diagnosticPolicy ambient administrative context scope output code
    fellThrough escaped registry faults
  definitions : layouts.definitions = ambient.definitions
  registered : frameLayout.Registered ambient.definitions
  escapedFault : faults .controlEscapedFunction escaped
  extend : ∀ {context next binder}, validity context → BinderExtends function.source.owner context binder next → validity next
  runtimeOf : ∀ {context}, validity context → CompatibleRuntimeContextValidity.Valid solved context function.evidence

/-- Compatibility projection retains the complete static body receipt. -/
def Origin.toStatic {values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (origin : Origin values ambient registry faults) : StaticOrigin values ambient registry faults where
  layouts := origin.layouts
  owner := origin.owner
  active := origin.active
  frameLayout := origin.frameLayout
  globals := origin.globals
  onError := origin.onError
  function := origin.function
  expressionSyntax := origin.expressionSyntax
  certificates := origin.certificates
  validity := origin.validity
  diagnosticPolicy := origin.diagnosticPolicy
  administrative := origin.administrative
  context := origin.context
  scope := origin.scope
  output := origin.output
  code := origin.code
  fellThrough := origin.fellThrough
  escaped := origin.escaped
  solved := origin.solved
  body := origin.body
  definitions := origin.definitions
  registered := origin.registered
  escapedFault := origin.escapedFault
  extend := origin.extend
  runtimeOf := origin.runtimeOf

namespace Stateful
universe u v
variable {Records : Type v}
  (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (conditionGate : Location → CallableIndexedHistory.NativeFrame → Prop)

structure Entry (origin : StaticOrigin values ambient registry faults)
    (functions : FunctionModel values.checked.catalog ambient) where
  mapping : LocationMap
  world : StoreTyping
  environment : Dynamic.Environment
  canonical : Environment
  actual : Environment
  heap : Dynamic.Heap
  store : Store
  embedding : Renaming
  actualContext : Core.Context
  frameLocation : Location
  native : CallableIndexedHistory.NativeFrame
  environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
    mapping world origin.administrative origin.scope environment canonical ambient.definitions
  heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store
  locals : Dynamic.EnvironmentAgrees heap origin.context.locals environment
  lookups : EnvironmentsAgree embedding canonical actual
  actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions
  reference : canonical[origin.scope.length + 1 + origin.globals]? = some (.cellRef origin.frameLayout.type frameLocation)
  read : store.read? frameLocation = some (SourceCoreCallableIndexedFrames.encode origin.frameLayout native)
  unmapped : frameLocation ∉ mapping
  initial : protocol.State ⟨origin.scope, mapping, world, heap, store, canonical⟩
  gate : conditionGate frameLocation native
variable (functions : FunctionModel values.checked.catalog ambient) (program : Program)
  (origin : StaticOrigin values ambient registry faults)

/-- The source body grade is the original grade. All reached state is retained. -/
def PreservesAt (size : Nat) : Prop :=
  ∀ (entry : Entry protocol conditionGate origin functions) {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap},
    RecursiveNamedCallBounds.BodyTrace program size origin.function origin.context entry.environment entry.heap outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates entry.actual entry.store (origin.code.rename entry.embedding) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld origin.function.resultType origin.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld origin.administrative program
        origin.function origin.context origin.scope entry.environment entry.heap after outcome ∧
      ProtectedStateTransition.Transition protocol entry.initial
        ⟨origin.scope, finalMap, finalWorld, after, finalStore, entry.canonical⟩

/-- Native completion supplies its own grade; the source grade is an output. -/
def ReflectsAt (size : Nat) : Prop :=
  ∀ (entry : Entry protocol conditionGate origin functions) {value : Value} {finalStore : Store},
    EvaluationSize size entry.actual entry.store (origin.code.rename entry.embedding) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize origin.function origin.context entry.environment entry.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld origin.function.resultType origin.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld origin.administrative program
        origin.function origin.context origin.scope entry.environment entry.heap after outcome ∧
      ProtectedStateTransition.Transition protocol entry.initial
        ⟨origin.scope, finalMap, finalWorld, after, finalStore, entry.canonical⟩

end Stateful

end Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyOrigins
