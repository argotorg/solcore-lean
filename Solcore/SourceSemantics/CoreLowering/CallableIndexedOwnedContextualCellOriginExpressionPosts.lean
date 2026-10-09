import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionBounds

/-! Model-generic admitted expression children already retain their result,
heap and actual reached state. Under the positive receiving model those first
two fields are positive result/cell receipts. Pure attachment records them in
PostWithOrigins at the same witness; forgetting reconstructs the original
child contract. This supplies no missing formation/read/call head or mutual
body law and changes neither the protocol nor either execution grade. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOriginExpressionPosts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedContextualCellOrigins (CellOrigins PostWithOrigins post_at_same_state)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- The receiving model itself carries positive closure origins through every
payload layer; an old general heap is not an input to this contract. -/
def model
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :=
  CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)

variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
  (certificate : GenericExpressionMeaning.Certificate)

/-- Source children retain the original input and grade and return the full
causal spine with their positive post inside the very same reached witness. -/
def PreservesAt (size : Nat) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node → ExpressionHasType source context id node.type →
  ∀ {mapping world administrative environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions →
    CellOrigins headers keys bodyRegistry registry faults profile mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions →
  ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      context evidence source environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents (model headers keys bodyRegistry registry faults profile)
        finalMap finalWorld node.type lowered.type faults outcome value ∧
      CellOrigins headers keys bodyRegistry registry faults profile finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        PostWithOrigins (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
          bridge context profile node.type lowered.type outcome value reached

/-- A native child keeps its measured native grade and independently returned
Source grade. No Source/native grade equality is introduced by attachment. -/
def ReflectsAt (size : Nat) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node → ExpressionHasType source context id node.type →
  ∀ {mapping world administrative environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions →
    CellOrigins headers keys bodyRegistry registry faults profile mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions →
  ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        context evidence source environment before id outcome after ∧
      GenericExpressionMeaning.ResultRepresents (model headers keys bodyRegistry registry faults profile)
        finalMap finalWorld node.type lowered.type faults outcome value ∧
      CellOrigins headers keys bodyRegistry registry faults profile finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        PostWithOrigins (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
          bridge context profile node.type lowered.type outcome value reached

/-- One actual original child producer supplies every witness. Attachment is
pure and performs no Source/native evaluation, allocation or restoration. -/
theorem preserves_at {size : Nat}
    (meaning : CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (model headers keys bodyRegistry registry faults profile) context evidence source certificate faults size) :
    PreservesAt (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      bridge profile context evidence source certificate size := by
  intro scope id lowered certified node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments cells locals agrees typed initial admitted trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalCells,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    meaning certified found sourceTyped environments cells locals agrees typed initial admitted trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalCells,
    maps, worlds, frame, metadata, reached, related,
    post_at_same_state bridge profile reached post finalCells represented⟩

/-- Reflection uses the original completed child exactly once and retains its
actual independently reconstructed Source trace and reached state. -/
theorem reflects_at {size : Nat}
    (meaning : CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (model headers keys bodyRegistry registry faults profile) context evidence source certificate faults size) :
    ReflectsAt (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      bridge profile context evidence source certificate size := by
  intro scope id lowered certified node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments cells locals agrees typed initial admitted completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalCells,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    meaning certified found sourceTyped environments cells locals agrees typed initial admitted completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalCells,
    maps, worlds, frame, metadata, reached, related,
    post_at_same_state bridge profile reached post finalCells represented⟩

/-- Pure forgetting feeds the existing Tree and lexical family ports without
changing the selected reached state or weakening the receiving heap model. -/
theorem PreservesAt.forget {size : Nat}
    (meaning : PreservesAt (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      bridge profile context evidence source certificate size) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (model headers keys bodyRegistry registry faults profile) context evidence source certificate faults size := by
  intro scope id lowered certified node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments cells locals agrees typed initial admitted trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalCells,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    meaning certified found sourceTyped environments cells locals agrees typed initial admitted trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalCells,
    maps, worlds, frame, metadata, reached, related, post.admission⟩

/-- The same native/source witnesses and all original effects survive
forgetting; only the added packaging around the real post is removed. -/
theorem ReflectsAt.forget {size : Nat}
    (meaning : ReflectsAt (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      bridge profile context evidence source certificate size) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (model headers keys bodyRegistry registry faults profile) context evidence source certificate faults size := by
  intro scope id lowered certified node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments cells locals agrees typed initial admitted completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalCells,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    meaning certified found sourceTyped environments cells locals agrees typed initial admitted completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalCells,
    maps, worlds, frame, metadata, reached, related, post.admission⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOriginExpressionPosts
