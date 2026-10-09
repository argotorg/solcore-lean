import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOrigins

/-! Positive callee leaves and actual initialized ordinary reads retain their
original raw Source type, native payload and reference. Compatible payload
wrappers preserve a runtime view of the original positive function leaf.
The closure branch retains its full Member; global and builtin branches retain
their original source-shaped receipts. No erased model is inverted. These pure
receipts supply no selected compiler code, generalized-cell classification,
callee execution or whole-call meaning. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCalleeOriginReadReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedContextualStoredClosureAssociationReceipts (Member)
open CallableIndexedOwnedContextualCellOrigins

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping}

/-- The raw occurrence or cell view remains separate from the retained positive
function leaf. Neither compatible raw views nor identical native carriers
identify the leaf's hidden Code or immutable owner. -/
def CalleeAt (raw : TypeSystem.Ty) (source : Dynamic.Value)
    (native : Core.Value) (type : Core.Ty) : Prop :=
  ∃ parameter result,
    SourceCoreRawMetadata.runtimeType raw =
      SourceCoreRawMetadata.runtimeType (.function parameter result) ∧
    FunctionOrigins headers keys bodyRegistry faults mapping world
      (.function parameter result) source native type

section Payload
variable (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {raw : TypeSystem.Ty} {source : Dynamic.Value} {native : Core.Value} {type : Core.Ty}

/-- Only the positive payload constructors and compatible wrappers are
projected. The actual Source callable variant is an independent shape receipt;
native type tags and erased general representation supply no classification. -/
theorem callable_at
    (payload : PayloadOrigins headers keys bodyRegistry registry faults profile
      mapping world raw source native type) :
    IsFunction source →
    CalleeAt (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry)
      (faults := faults) (mapping := mapping) (world := world) raw source native type := by
  induction payload using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) with
  | function positive => intro _; exact ⟨_, _, rfl, positive⟩
  | compatible same inner ih =>
      intro callable
      obtain ⟨parameter, result, view, positive⟩ := ih callable
      exact ⟨parameter, result, same.trans view, positive⟩
  | unit | bool | word | integer | product | proxy | constructed | mappingValue =>
      intro callable
      cases callable
  | nil | cons | empty | entry | absent | present => trivial

/-- Closure classification retains the exact Member already carried by the
positive leaf, even when the original raw type has compatible wrappers. -/
theorem CalleeAt.closure_member {function : Dynamic.Closure}
    (callee : CalleeAt (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry)
      (faults := faults) (mapping := mapping) (world := world) raw (.closure function) native type) :
    ∃ bindings parameter result,
      Member headers keys bodyRegistry faults mapping world function native bindings parameter result ∧
      type = CallableContract.functionType parameter result ∧
      SourceCoreRawMetadata.runtimeType raw =
        SourceCoreRawMetadata.runtimeType (FunctionValues.sourceType function) := by
  obtain ⟨_, _, view, positive⟩ := callee
  cases positive with
  | closure member => exact ⟨_, _, _, member, rfl, view⟩

/-- Global classification keeps the exact original named-function receipt at
the function leaf and the independent compatible raw view. -/
theorem CalleeAt.global_receipt {function : Dynamic.GlobalFunction}
    (callee : CalleeAt (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry)
      (faults := faults) (mapping := mapping) (world := world) raw (.global function) native type) :
    ∃ parameter result,
      SourceCoreRawMetadata.runtimeType raw =
        SourceCoreRawMetadata.runtimeType (.function parameter result) ∧
      CallableIndexedOwnedGeneralLambdaValues.Represents headers keys bodyRegistry faults
        mapping world (.function parameter result) (.global function) native type := by
  obtain ⟨parameter, result, view, positive⟩ := callee
  cases positive with
  | global related => exact ⟨parameter, result, view, related⟩

/-- Builtins retain their original source-shaped receipt; no closure branch
or body syntax is manufactured for them. -/
theorem CalleeAt.builtin_receipt {function : Dynamic.BuiltinFunction}
    (callee : CalleeAt (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry)
      (faults := faults) (mapping := mapping) (world := world) raw (.builtin function) native type) :
    ∃ parameter result,
      SourceCoreRawMetadata.runtimeType raw =
        SourceCoreRawMetadata.runtimeType (.function parameter result) ∧
      CallableIndexedOwnedGeneralLambdaValues.Represents headers keys bodyRegistry faults
        mapping world (.function parameter result) (.builtin function) native type := by
  obtain ⟨parameter, result, view, positive⟩ := callee
  cases positive with
  | builtin related => exact ⟨parameter, result, view, related⟩
end Payload

section Read
variable (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {heap : Dynamic.Heap} {store : Store}

/-- This receipt is indexed by the same actual cell, mapping, world and stores.
The raw cell type is retained rather than replaced by a closure's source type. -/
structure InitializedReadAt (location : Dynamic.Location) (raw : TypeSystem.Ty)
    (source : Dynamic.Value) (target : Core.Location) (native : Core.Value)
    (type : Core.Ty) : Prop where
  source_read : Dynamic.Heap.Reads heap location ⟨raw, some source, none⟩
  reference : ReferenceRepresents mapping world location target type
  native_read : store.read? target = some (.inRight .unit native)
  payload : PayloadOrigins headers keys bodyRegistry registry faults profile
    mapping world raw source native type

/-- One original generic heap read extracts the actual optional cell and its
positive payload. This constructs no Source or native execution. -/
theorem initialized_read_at {location : Dynamic.Location} {raw : TypeSystem.Ty}
    {source : Dynamic.Value}
    (cells : CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store)
    (read : Dynamic.Heap.Reads heap location ⟨raw, some source, none⟩) :
    ∃ target native type,
      InitializedReadAt (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry)
        (registry := registry) (faults := faults) (mapping := mapping) (world := world)
        (heap := heap) (store := store) profile location raw source target native type := by
  obtain ⟨target, optional, type, reference, nativeRead, represented⟩ := cells.read read
  cases represented with
  | initialized payload => exact ⟨target, _, type, read, reference, nativeRead, payload⟩

/-- A genuine occurrence/declaration raw view wraps only the retained payload.
The actual cell and both reads remain indexed by their original raw cell type. -/
theorem InitializedReadAt.payload_at_view
    {location : Dynamic.Location} {raw occurrence : TypeSystem.Ty}
    {source : Dynamic.Value} {target : Core.Location} {native : Core.Value} {type : Core.Ty}
    (read : InitializedReadAt (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry)
      (registry := registry) (faults := faults) (mapping := mapping) (world := world)
      (heap := heap) (store := store) profile location raw source target native type)
    (view : SourceCoreRawMetadata.runtimeType occurrence = SourceCoreRawMetadata.runtimeType raw) :
    PayloadOrigins headers keys bodyRegistry registry faults profile mapping world
      occurrence source native type :=
  .compatible view read.payload

/-- The initialized closure branch extracts its Member at this exact read,
without requiring raw = FunctionValues.sourceType function. -/
theorem InitializedReadAt.closure_member
    {location : Dynamic.Location} {raw : TypeSystem.Ty} {function : Dynamic.Closure}
    {target : Core.Location} {native : Core.Value} {type : Core.Ty}
    (read : InitializedReadAt (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry)
      (registry := registry) (faults := faults) (mapping := mapping) (world := world)
      (heap := heap) (store := store) profile location raw (.closure function) target native type) :
    ∃ bindings parameter result,
      Member headers keys bodyRegistry faults mapping world function native bindings parameter result ∧
      type = CallableContract.functionType parameter result ∧
      SourceCoreRawMetadata.runtimeType raw =
        SourceCoreRawMetadata.runtimeType (FunctionValues.sourceType function) :=
  (callable_at profile read.payload (.closure function)).closure_member
end Read
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCalleeOriginReadReceipts
