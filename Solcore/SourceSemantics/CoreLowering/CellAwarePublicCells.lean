import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalDescriptorHeap
import Solcore.SourceSemantics.CoreLowering.CompatibleAmbientHeap

/-! The actual receiver may extend raw metadata while retaining the same
ordinary values and generalized descriptors at their original locations. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicCells
open Core Frontend GeneralHeap CompatiblePayload

abbrev Family (definitions : DataEnvironment) :=
  SourceCoreRawMetadata.Registry → GenericHeap.CellModel definitions

/-- This law only transports cell representation along a forward metadata
extension. It does not supply expression, body or invocation semantics. -/
def ExtendsRegistry {definitions : DataEnvironment} (cells : Family definitions) : Prop :=
  ∀ {registry future}, SourceCoreRawMetadata.Extends registry future →
    ∀ {mapping world cell value payload},
      (cells registry).Represents mapping world cell value payload →
      (cells future).Represents mapping world cell value payload

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {ambient : AmbientDefinitions checked.catalog.definitions}

def generalized (functions : FunctionModel checked.catalog ambient)
    (instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions) :
    Family ambient.definitions :=
  fun registry => GeneralizedLocalDescriptorHeap.cellModel
    (CompatibleAmbientHeap.payloadModel checked registry functions) instances

theorem generalized_extends_registry
    (functions : FunctionModel checked.catalog ambient)
    (instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions) :
    ExtendsRegistry (generalized functions instances) := by
  intro registry future extension mapping world cell value payload represented
  cases represented with
  | ordinary prior => exact .ordinary (CompatibleHeap.cell_extend_registry prior extension)
  | generalized stored => exact .generalized stored

/-- Initial ordinary cells embed at the same Source/native heap. There is no
conversion in the reverse direction for a heap containing descriptors. -/
theorem generalized_initial
    {functions : FunctionModel checked.catalog ambient}
    (instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions)
    {registry : SourceCoreRawMetadata.Registry} {mapping : LocationMap} {world : StoreTyping}
    {heap : Dynamic.Heap} {store : Store}
    (related : CompatibleAmbientHeap.HeapRepresents checked registry functions mapping world heap store) :
    GenericHeap.CellHeapRepresents (generalized functions instances registry) mapping world heap store :=
  GeneralizedLocalDescriptorHeap.initial related

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicCells
