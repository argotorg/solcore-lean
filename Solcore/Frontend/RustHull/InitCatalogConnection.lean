import Solcore.Frontend.RustHull.ContractCallModeSupported
import Solcore.Frontend.RustHull.ChildFrameModeSemantics
import Solcore.Frontend.RustHull.DerivationCorrespondenceSupport

/-! The premise that links a source init catalog to the compiled catalog. The
source init templates are the compiled init definitions, in catalog order, with
the same program, object and init bytes; each runtime image a source deployment
may install is a runtime image of the compiled object; and the catalog is small
enough that the identities `index + 2` of its entries are distinct words. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.InitCatalogCorrespondence

/-- The compiled init definitions with their catalog indices, in catalog order,
as the actual `runInit` selects among them. -/
def initDefinitions (catalog : List AccountRuntime.CodeDefinition) : List (AccountRuntime.CodeDefinition × Nat) :=
  catalog.zipIdx.filter fun (definition, _) => definition.isInit

/-- The runtime images the actual installation identifies: the root image and
the catalog entries that are not init definitions. -/
def runtimeImages (image : Option (List UInt8)) (catalog : List AccountRuntime.CodeDefinition) :
    List (List UInt8) :=
  image.toList ++ (catalog.filter fun definition => !definition.isInit).map AccountRuntime.CodeDefinition.bytes

def InitCatalogConnection (initCatalog : ChildFrameSemantics.InitCatalog) (image : Option (List UInt8))
    (catalog : List AccountRuntime.CodeDefinition) : Prop :=
  initCatalog.templates.length = (initDefinitions catalog).length ∧
  (∀ (position : Nat) (source : ChildFrameSemantics.Code), initCatalog.templates[position]? = some source →
    ∃ (definition : AccountRuntime.CodeDefinition) (index : Nat),
      (initDefinitions catalog)[position]? = some (definition, index) ∧
      source.program = definition.program ∧
      AccountRuntime.select definition.program.objects definition.path = .ok source.body ∧
      source.bytes = definition.bytes ∧
      DerivationCorrespondence.ExecutableProgram (ContractCallModeCorrespondence.supported true) source.functions) ∧
  (∀ bytes ∈ initCatalog.runtimes, bytes ∈ runtimeImages image catalog) ∧
  catalog.length + 2 < Core.wordModulus

/-- A program that creates nothing links the empty init catalog to any catalog
without init definitions. -/
theorem InitCatalogConnection.empty {image : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition}
    (noInit : initDefinitions catalog = []) (small : catalog.length + 2 < Core.wordModulus) :
    InitCatalogConnection {} image catalog := by
  refine ⟨by simp [noInit], ?_, ?_, small⟩
  · intro position source found
    simp at found
  · intro bytes member
    simp at member

end Solcore.Frontend.RustHull.InitCatalogCorrespondence
