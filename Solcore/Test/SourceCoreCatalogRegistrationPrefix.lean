import Solcore.SourceSemantics.CoreLowering.CompatibleCatalogRegistrationPrefix

/-! Existing entry records, identities and native derivations survive the real
registration traversal. Recursive nominal/mapping payloads exercise fresh
reservations and the final install at their original reserved indices. -/
set_option autoImplicit false
namespace Tests.SourceCoreCatalogRegistrationPrefix
open Solcore Core Frontend SourceInference SourceSemantics.CoreLowering
open SourceCoreCompatibleCatalog CompatibleCatalogRegistrationPrefix

theorem actual_registration_preserves_native
    {signatures : ProgramSignatures} {fuel : Nat} {before after : Catalog}
    {original : TypeSystem.Ty} {native : Ty} {context : Core.Context} {code : Expr} {type : Ty}
    (accepted : registerType signatures fuel before original = .ok (after, native))
    (wellFormed : type.WellFormed before.definitions)
    (typed : HasType context code type before.definitions) :
    type.WellFormed after.definitions ∧ HasType context code type after.definitions :=
  ⟨wellFormed.extend_definitions (registerType_definitions accepted),
    typed.extend_definitions (registerType_definitions accepted)⟩

theorem actual_registration_preserves_constructor
    {signatures : ProgramSignatures} {fuel : Nat} {before after : Catalog}
    {originals : List TypeSystem.Ty} {natives : List Ty} {constructor : ConstructorId} {payload : Ty}
    (accepted : registerTypes signatures fuel before originals = .ok (after, natives))
    (found : before.definitions.lookupConstructorPayloadType? constructor = some payload) :
    after.definitions.lookupConstructorPayloadType? constructor = some payload :=
  (registerTypes_definitions accepted).constructor_lookup found

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"catalog_prefix", by decide⟩], by decide⟩⟩
private def owner (index : Nat) : Resolved.DeclarationId := ⟨moduleId, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "catalog_prefix.solc"⟩, 0, 1⟩
private def nominal (index : Nat) : TypeSystem.Ty := .nominal (owner index) []
private def constructor (dataIndex position : Nat) (name : String) (payloads : List TypeSystem.Ty) : ProgramDataConstructorSignature :=
  ⟨⟨owner dataIndex, position⟩, name, payloads, ⟨span, ⟨[], ⟨span, name⟩, none⟩⟩⟩
private def signature (index : Nat) (name : String) (constructors : List ProgramDataConstructorSignature) : ProgramDataSignature :=
  {id := owner index, name, parameters := [], constructors,
   source := ⟨span, ⟨none, ⟨span, name⟩, none, span, []⟩⟩}
private def signatures : ProgramSignatures := ⟨[], [], [], [], [
  signature 0 "Tree" [constructor 0 0 "Leaf" [.bool], constructor 0 1 "Branch" [nominal 0, nominal 0]],
  signature 1 "Left" [constructor 1 0 "Left" [nominal 2]],
  signature 2 "Right" [constructor 2 0 "Right" [nominal 1, .mapping (.product .bool .bool) (nominal 0)]],
  signature 3 "Box" [constructor 3 0 "Box" [.function .word (nominal 0), .proxy (.comptime .bool)]]
], []⟩

private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def entryView (entry : Entry) : TypeSystem.Ty × Option DataDefinition × List ProgramDataConstructorId :=
  (entry.sourceType, entry.definition, entry.constructors)

def run : IO Unit := do
  for callableContracts in [true, false] do
    let (initial, _) ← get "initial registered tree"
      (registerType signatures 100 {callableContracts} (nominal 0))
    require (initial.entries.length == 1 && initial.entries.all (fun entry => entry.definition.isSome))
      "self recursion did not reuse its reserved identity"
    let treeIdentity := initial.identity? (nominal 0)
    let treeDefinition := initial.definitions[0]?
    let (extended, _) ← get "mutual recursive and compound registration"
      (registerTypes signatures 100 initial [nominal 1, nominal 3, .mapping (nominal 0) .word])
    require (decide ((extended.entries.take initial.entries.length).map entryView = initial.entries.map entryView) &&
      decide (extended.definitions[0]? = treeDefinition) &&
      decide (extended.identity? (nominal 0) = treeIdentity))
      "registration changed the existing complete entry or native identity"
    require (extended.entries.all (fun entry => entry.definition.isSome) &&
      extended.definitions.isWellFormed && extended.callableContracts == callableContracts)
      "recursive payload registration left unfinished definitions or changed the callable profile"
    let (repeated, _) ← get "repeat existing identity at zero fuel"
      (registerType signatures 0 extended (.comptime (nominal 0)))
    require (decide (repeated.entries.map entryView = extended.entries.map entryView)) "existing runtime identity allocated a duplicate entry"
  IO.println "compatible catalog registration: exact existing prefixes, recursive reserved identities, compound payloads and both callable profiles GREEN"

end Tests.SourceCoreCatalogRegistrationPrefix
