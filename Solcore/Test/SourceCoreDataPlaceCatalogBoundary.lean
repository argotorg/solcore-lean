import Solcore.SourceSemantics.CoreLowering.DataPlaceGetterTyping

/-! Finite well-formed Core definitions do not authenticate nominal catalog
row completeness. The real entry checker must retain that separate boundary. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace Tests.SourceCoreDataPlaceCatalogBoundary
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open SourceCoreDataPlaces

private def moduleId : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"place_catalog", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def dataId : Resolved.DeclarationId := ⟨moduleId, 1⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "place_catalog.solc"⟩, 0, 1⟩
private def site : SourceCoreElaboration.ErrorSite := .occurrence ⟨owner, 0⟩
private def boxType : TypeSystem.Ty := .nominal dataId []
private def signature : ProgramDataSignature := {
  id := dataId, name := "Box", parameters := []
  constructors := [⟨⟨dataId, 0⟩, "Box", [.integer], ⟨span, ⟨[], ⟨span, "Box"⟩, none⟩⟩⟩]
  source := ⟨span, ⟨none, ⟨span, "Box"⟩, none, span, []⟩⟩ }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [signature], []⟩
private def catalog : SourceCoreDataCatalog.Catalog := { entries := [
  { sourceType := boxType, definition := some ⟨[.integer, .integer]⟩, constructors := [⟨dataId, 0⟩] }] }
private def checked : SourceCoreDataCatalog.Checked :=
  ⟨catalog, Core.DataEnvironment.isWellFormed_sound (by decide)⟩
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "root", .mono boxType, [], false, none⟩
private def source : TypedSource := { owner, inputs := [binder], roots := [], nodes := [] }
private def assignment : AssignmentResolution := ⟨⟨binder.id, [.member "field" 0], .integer⟩, []⟩
private def route : Route := ⟨boxType, .namedData ⟨0⟩, .integer,
  [.member ⟨0⟩ 0 [⟨⟨⟨0⟩, 0⟩, [.integer]⟩] .integer], none⟩
private def prepared : Prepared := ⟨route, [.member ⟨0⟩ 0 [⟨⟨⟨0⟩, 0⟩, [.integer]⟩] .integer], [], Word.zero⟩

example : describe checked signatures source site assignment = .ok route := by cbv
example : prepare checked 20 route Word.zero (fun _ => Word.zero) = .ok prepared := by cbv

/-- The compiler produced one branch from the one genuine source constructor,
while the merely finite-well-formed catalog declares two Core alternatives. -/
example : infer? [] (getter prepared .unit) catalog.definitions = none := by cbv

/-- This is rejected statically; it is not a source-program runtime fault. -/
example : ¬ ∃ type, HasType [] (getter prepared .unit) type catalog.definitions := by
  rintro ⟨type, typed⟩
  have inferred := infer_complete typed
  have absent : infer? [] (getter prepared .unit) catalog.definitions = none := by cbv
  rw [absent] at inferred
  cases inferred

end Tests.SourceCoreDataPlaceCatalogBoundary
