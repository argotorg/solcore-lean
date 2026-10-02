import Solcore.SourceSemantics.CoreLowering.CompatibleCatalogNominalCoverage

/-! Factory provenance excludes extra native constructor branches. Both
callable profiles and self/mutual recursive nominal payloads are exercised.
Well-formed native definitions alone do not imply this source correspondence. -/
set_option autoImplicit false
namespace Tests.SourceCoreCatalogNominalCoverage
open Solcore Core Frontend SourceInference SourceSemantics.CoreLowering
open SourceCoreCompatibleCatalog CompatibleCatalogNominalCoverage

theorem actual_factory_has_complete_nominal_coverage
    {signatures : ProgramSignatures} {fuel : Nat} {types : List TypeSystem.Ty}
    {metadata : List Metadata} {limits : Limits} {callableContracts : Bool} {checked : Checked}
    (accepted : prepare signatures fuel types metadata limits callableContracts = .ok checked)
    {original : TypeSystem.Ty} {declaration : Resolved.DeclarationId} {arguments : List TypeSystem.Ty}
    {signature : ProgramDataSignature} {identity : DataTypeId} {definition : DataDefinition}
    (nominal : SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType original) = some (declaration, arguments))
    (selected : checked.signatures.dataTypes.filter (fun data => decide (data.id = declaration)) = [signature])
    (found : checked.catalog.identity? original = some identity)
    (registered : checked.catalog.definitions.lookupDataType? identity = some definition) :
    definition.constructorPayloadTypes.length = signature.constructors.length := by
  obtain ⟨_, _, _, coverage⟩ := prepare_nominal_coverage accepted nominal selected found registered
  exact coverage

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"catalog_coverage", by decide⟩], by decide⟩⟩
private def owner (index : Nat) : Resolved.DeclarationId := ⟨moduleId, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "catalog_coverage.solc"⟩, 0, 1⟩
private def nominal (index : Nat) : TypeSystem.Ty := .nominal (owner index) []
private def constructor (dataIndex position : Nat) (name : String) (payloads : List TypeSystem.Ty) : ProgramDataConstructorSignature :=
  ⟨⟨owner dataIndex, position⟩, name, payloads, ⟨span, ⟨[], ⟨span, name⟩, none⟩⟩⟩
private def signature (index : Nat) (name : String) (constructors : List ProgramDataConstructorSignature) : ProgramDataSignature :=
  {id := owner index, name, parameters := [], constructors,
   source := ⟨span, ⟨none, ⟨span, name⟩, none, span, []⟩⟩}
private def tree : ProgramDataSignature :=
  signature 0 "Tree" [constructor 0 0 "Leaf" [.bool], constructor 0 1 "Branch" [.bool, nominal 0, nominal 0]]
private def signatures : ProgramSignatures := ⟨[], [], [], [], [
  tree,
  signature 1 "Left" [constructor 1 0 "Left" [nominal 2]],
  signature 2 "Right" [constructor 2 0 "Right" [nominal 1, .mapping (.product .bool .bool) (nominal 0)]],
  signature 3 "Box" [constructor 3 0 "Box" [.function .word (nominal 0), .proxy (.comptime .bool)]],
  signature 4 "Empty" []
], []⟩

private def forged : Catalog := {
  entries := [⟨nominal 0, some ⟨[.word, .word, .word]⟩, tree.constructors.map (·.id)⟩]
}

theorem native_wellFormed_allows_extra_constructor : forged.definitions.WellFormed := by
  apply DataEnvironment.isWellFormed_sound
  decide

theorem forged_native_wellFormed_does_not_supply_coverage : ¬ Shapes signatures forged := by
  intro shaped
  obtain ⟨actual, selected, _, count⟩ := shaped _ (List.mem_cons_self)
    (owner 0) [] (by rfl)
  have same : actual = tree := by
    simpa [signatures, tree, signature, owner, moduleId] using selected.symm
  subst actual
  have impossible := count ⟨[.word, .word, .word]⟩ rfl
  contradiction

private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def run : IO Unit := do
  for callableContracts in [true, false] do
    let checked ← get "actual completed catalog factory"
      (prepare signatures 200 [nominal 0, nominal 1, nominal 3, nominal 4, .mapping (nominal 0) .word]
        [] {} callableContracts)
    require (checked.catalog.definitions.isWellFormed &&
      checked.catalog.entries.all (fun entry => entry.definition.isSome)) "factory left an unfinished reservation"
    for data in signatures.dataTypes do
      let identity ← match checked.catalog.identity? (.nominal data.id []) with
        | some identity => pure identity
        | none => throw (IO.userError "actual nominal identity missing")
      let entry ← match checked.catalog.entries[identity.index]? with
        | some entry => pure entry
        | none => throw (IO.userError "actual nominal entry missing")
      let definition ← match checked.catalog.definitions.lookupDataType? identity with
        | some definition => pure definition
        | none => throw (IO.userError "actual native definition missing")
      require (decide (entry.constructors = data.constructors.map (·.id)) &&
        definition.constructorPayloadTypes.length == data.constructors.length)
        "factory changed the exact nominal constructor inventory or native branch coverage"
    require (checked.catalog.callableContracts == callableContracts) "factory changed its callable representation"
  require (forged.definitions.isWellFormed &&
    ((forged.definitions[0]?).getD (DataDefinition.mk [])).constructorPayloadTypes.length != tree.constructors.length)
    "negative well-formed catalog fixture did not retain an extra native constructor"
  IO.println "compatible nominal catalog coverage: actual factory, complete inventories, recursive reservations, both profiles and forged extra constructors GREEN"

end Tests.SourceCoreCatalogNominalCoverage
