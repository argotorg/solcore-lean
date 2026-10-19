import Solcore.Test.SourceCoreGeneralizedExportMaterialized

/-! Finite output selections expose the actual Source/native leaves of the
original pair and single factory returns. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)
open RecursiveNamedPublicOutputSelections (Selection Selected)

def pairSelection {type leftType rightType : TypeSystem.Ty} {value : SourceCorePublicValues.Value}
    {left right : SourceCorePublicValues.Handle}
    (types : type = .product leftType rightType)
    (values : value = .product (.function left) (.function right)) : Selection type value := by
  cases types
  cases values
  exact .product .function .function

theorem pairSelection_handles {type leftType rightType : TypeSystem.Ty} {value : SourceCorePublicValues.Value}
    {left right : SourceCorePublicValues.Handle}
    (types : type = .product leftType rightType)
    (values : value = .product (.function left) (.function right)) :
    (pairSelection types values).handles = [left,right] := by
  cases types
  cases values
  rfl

theorem pair_selected {type leftType rightType : TypeSystem.Ty} {value : SourceCorePublicValues.Value}
    {left right : SourceCorePublicValues.Handle}
    (types : type = .product leftType rightType)
    (values : value = .product (.function left) (.function right))
    {first second : Dynamic.Value} {native : Core.Value} {nativeType : Core.Ty} {fuel : Nat} {entries : List Entry}
    (selected : Selected (pairSelection types values) (.product first second) native nativeType fuel entries) :
    ∃ firstNative secondNative firstType secondType remaining,
      entries = [⟨leftType,first,left,firstNative,firstType,remaining⟩,
        ⟨rightType,second,right,secondNative,secondType,remaining⟩] := by
  cases types
  cases values
  cases selected with
  | product leftSelected rightSelected =>
    cases leftSelected
    cases rightSelected
    exact ⟨_,_,_,_,_,rfl⟩

def functionSelection {type : TypeSystem.Ty} {value : SourceCorePublicValues.Value}
    {handle : SourceCorePublicValues.Handle} (same : value = .function handle) : Selection type value := by
  cases same
  exact .function

theorem function_selected {type : TypeSystem.Ty} {value : SourceCorePublicValues.Value}
    {handle : SourceCorePublicValues.Handle} (same : value = .function handle)
    {source : Dynamic.Value} {native : Core.Value} {nativeType : Core.Ty} {fuel : Nat} {entries : List Entry}
    (selected : Selected (functionSelection (type := type) same) source native nativeType fuel entries) :
    entries = [⟨type,source,handle,native,nativeType,fuel⟩] := by
  cases same
  cases selected
  rfl

theorem skip_selected {type : TypeSystem.Ty} {value : SourceCorePublicValues.Value}
    {source : Dynamic.Value} {native : Core.Value} {nativeType : Core.Ty} {fuel : Nat} {entries : List Entry}
    (selected : Selected (Selection.skip (type := type) (value := value)) source native nativeType fuel entries) :
    entries = [] := by
  cases selected
  rfl

end Tests.SourceCoreGeneralizedExport
