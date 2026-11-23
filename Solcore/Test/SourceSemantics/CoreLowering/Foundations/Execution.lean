import Solcore.Test.SourceSemantics.CoreLowering.Canonical.Scoped
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.NamedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.MappingsAndEquality
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Payloads
import Solcore.Frontend.SourceCompiler
import Solcore.Frontend.SourceCoreCompiler
import Solcore.Test.SourceSemantics.CoreLowering.Method.OriginFixture
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.OrdinaryCatalog
import Solcore.Test.Frontend.Source.CompilerFeatureSupport
import Solcore.Frontend.SourceCore.GeneralFunctions
import Solcore.Frontend.SourceCore.Internal.CallableViews
import Solcore.Frontend.ProgramChecking
import Solcore.Frontend.SourceCore.RawMetadata
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NamedCollectors
import Solcore.Test.SourceSemantics.CoreLowering.Canonical.Formation
import Solcore.Test.SourceSemantics.CoreLowering.Constructor
import Solcore.Frontend.SourceCore.Internal.Entries
import Solcore.Frontend.SourceCoreIndexedSession
import Solcore.Test.SourceSemantics.CoreLowering.Method.OriginEvidence
import Solcore.Test.SourceSemantics.CoreLowering.LexicalFailure
import Solcore.Frontend.SourceCore.CompatibleCatalog
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.BasicExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.GeneralExpressions
import Solcore.Frontend.SourceCoreExecution
import Solcore.Frontend.SourceCore.Lowering
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.LambdaViewsAndMarkedCaptures
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.SourceStaging
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.ControlStatements
import Solcore.Frontend.SourceCoreElaboration
import Solcore.Core.Machine

/-!
# Lowering execution tests

Elaboration to Core, staged execution and meaning, and small catalog regressions.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreAcceptedBodyBindings
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Tests.SourceCoreAcceptedBodyBindings
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open AcceptedNamedBodyFlow
open Tests.SourceCoreCanonicalScoped

private theorem let_return {policy : SourceCoreLoops.Policy} {checked : SourceCoreCompatibleCatalog.Checked}
    {source : TypedSource} {result : Ty} {reasonAt : ExpressionId → Word} {mode : Bool} {escaped : Word}
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {code : Expr} {statements : List StatementId}
    {initialized returned : StatementNode} {binder : TypedBinder} {initializer expression : ExpressionId}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code)
    (roots : statements = [initialized.id, returned.id])
    (reader : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (initialFound : source.lookupStatement? initialized.id = some initialized)
    (initialForm : initialized.form = .letDecl binder (some initializer))
    (returnFound : source.lookupStatement? returned.id = some returned)
    (returnForm : returned.form = .returnStmt (some expression)) :
    tree.closed = true ∧ tree.bindings.map (·.binder) = [binder] := by
  subst statements
  cases tree with
  | initialized read form _ projected child generated _ remaining allocated =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans initialFound)
      cases same
      rw [initialForm] at form
      cases form
      have tail := remaining.at_return reader returnFound returnForm
      simp only [Tree.closed, Tree.bindings, List.map_cons, tail.1, tail.2.1, List.map_nil,
        and_self]
  | returning read form | returnUnit read form | absent read form
  | assigning read form | assigned read form | projectedAssigned read form | whileLoop read form
  | bitNotting read form | bitNotted read form | projectedBitNotted read form
  | discard read form | block read form | conditional read form
  | valueDiscard read form
  | matching read form | matched read form
  | forLoop read form | forBoundary read form | breaking read form | continuing read form =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans initialFound)
      cases same
      simp_all
  | boundary read outside accepted =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans initialFound)
      cases same
      simp only [initialForm, expanded] at outside
      cases outside

/-- The real cached H relay has one compiler-issued binding. Its declaration
receipt comes from original Header typing, without a supplied binder callback. -/
theorem relay_receipts {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.relayRow.row) :
    ∃ receipt : AcceptedNamedBodyAdmission.BodyAt actual.header,
      receipt.tree.closed = true ∧
      receipt.tree.bindings.map (·.binder) = [observed.relayShape.localBinder] ∧
      (∀ binding ∈ receipt.tree.bindings,
        RecursiveNamedStatementSyntaxFacts.BinderReceipt actual.header.function.source binding.binder) := by
  obtain ⟨receipt⟩ := body_of_accepted actual.aligned.accepted
  have roots := actual.relay_body (observed := observed)
  have source := actual.source
  have details : receipt.tree.closed = true ∧
      receipt.tree.bindings.map (·.binder) = [observed.relayShape.localBinder] := by
    exact let_return receipt.tree roots (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read actual.prepared actual.aligned)
      (by rw [source]; exact observed.relayShape.initializedFound)
      observed.relayShape.initializedForm
      (by rw [source]; exact observed.relayShape.statementFound)
      observed.relayShape.statementForm
  have mono : ∀ binding ∈ receipt.tree.bindings, binding.binder.scheme.quantified = [] := by
    intro binding member
    have present : binding.binder ∈ receipt.tree.bindings.map (·.binder) :=
      List.mem_map.mpr ⟨binding, member, rfl⟩
    rw [details.2] at present
    have same := List.mem_singleton.mp present
    rw [same, observed.relayShape.localScheme]
    rfl
  rcases AcceptedNamedBodyBindings.of_header actual.prepared actual.aligned fixture.source_wellFormed receipt.tree with receipts | boundary
  · exact ⟨receipt, details.1, details.2, receipts⟩
  · obtain ⟨binding, member, quantified⟩ := boundary
    exact False.elim (quantified (mono binding member))

theorem observed_receipts (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    ∃ actual : ActualHeader fixture observed.relayRow.row,
      ∃ receipt : AcceptedNamedBodyAdmission.BodyAt actual.header,
        receipt.tree.closed = true ∧
        receipt.tree.bindings.map (·.binder) = [observed.relayShape.localBinder] ∧
        (∀ binding ∈ receipt.tree.bindings,
          RecursiveNamedStatementSyntaxFacts.BinderReceipt actual.header.function.source binding.binder) := by
  obtain ⟨input, row, packet, actual, rest⟩ := observed.relayRow.issue
  exact ⟨actual, relay_receipts actual⟩

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  have _receipts := observed_receipts fixture observed
  IO.println "ACCEPTED_BODY_BINDINGS_PASS: actual H let/direct/return, one original monomorphic local, exact compiler flow and Header-derived declaration"

end Tests.SourceCoreAcceptedBodyBindings
end

section
-- leanmerge: from Solcore.Test.SourceCoreCatalogNominalCoverage
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreCatalogRegistrationPrefix
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompilationScope
/-! Selected compilation keeps unrelated inference-only declarations in the
checked source program. Public execution uses the selected dependency closure. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCompilationScope
open Solcore Frontend SourceInference

def source : String := String.intercalate "\n" [
  "trait Coerce<From, To> {}",
  "enum Box { Only }",
  "impl Coerce<Word, Box> {}",
  "function convert(value: Word) returns (Box) { return value; }",
  "function identity(value: Word) returns (Word) { return value; }"
]

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content := "pragma solcore;\n" ++ source }]
  externalLibraries := []
}

def options : SourceCompiler.Options := {
  checkingFuel := 1000, compilationFuel := 1000, specializationBudget := 256
}

def run : IO Unit := do
  let program ← match checkProgram workspace options.checkingFuel with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"scope fixture rejected by checker: {reprStr errors}")
  unless program.functions.length == 2 && program.methods.isEmpty do
    throw (IO.userError "scope fixture changed its declaration inventory")
  let some conversion := program.signatures.functions.find? (fun row => row.name == "convert")
    | throw (IO.userError "conversion signature missing")
  let some identity := program.signatures.functions.find? (fun row => row.name == "identity")
    | throw (IO.userError "identity signature missing")
  match SourceCompiler.compileChecked program [.declaration conversion.id] options with
  | .error (.compilation (.planEvidence (.executableCoercionMethod _ _ _
      (.missingTraitMethod _ "coerce")))) => pure ()
  | .error error => throw (IO.userError s!"unexpected conversion failure: {reprStr error}")
  | .ok _ => throw (IO.userError "conversion without an executable method was accepted")
  let compiled ← match SourceCompiler.compileChecked program [.declaration identity.id] options with
    | .ok compiled => pure compiled
    | .error error => throw (IO.userError s!"unrelated selected function rejected: {reprStr error}")
  unless compiled.program.functions.length == 2 do
    throw (IO.userError "compilation discarded the original source program")
  unless compiled.plan.specializations.map (·.declaration) == [identity.id] do
    throw (IO.userError "unselected conversion entered the specialization plan")
  let [key] := compiled.keys | throw (IO.userError "selected root inventory changed")
  let artifact ← compiled.open
  let bootstrap ← artifact.bootstrap
  let .ready session := bootstrap.resume 10000
    | throw (IO.userError "selected scope initialization did not complete")
  match ← session.run key [.word (Core.Word.ofNatModulo 37)]
      { executionFuel := 10000 } with
  | .ok (.succeeded completion) =>
      unless completion.value == .word (Core.Word.ofNatModulo 37) do
        throw (IO.userError "selected scope returned the wrong value")
  | _ => throw (IO.userError "selected scope public execution did not succeed")
  IO.println "COMPILATION_SCOPE_BOUNDARY_PASS"

end Tests.SourceCoreCompilationScope
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompiler
#check_failure Solcore.Frontend.SourceCoreCompiler.Options.backendPreference
#check_failure Solcore.Frontend.SourceCoreCompiler.Compiled.mk
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! One cached compiler artifact serves ordered and duplicate roots. Source
metadata comes from canonical specialization; raw mapping carriers remain a
compatibility observation used only to exercise the cached code here. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompiler
open Solcore Solcore.Frontend SourceCoreCompiler

private def w (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := "pragma solcore;\n" ++ String.intercalate "\n" [
    "function identity<T>(value: T) returns (T) { return value; }",
    "function mappingEcho(value: mapping(Word => Word)) returns (mapping(Word => Word)) { return value; }",
    "function capture(seed: Word) returns (function(Word) returns (Word)) { let current = seed; return lam(step: Word) { current += step; return current; }; }"
  ]}] }
private def options : Options := { specializationBudget := 256, compilationFuel := 1000 }
private def declaration (program : CheckedProgram) (name : String) : IO Resolved.DeclarationId :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure signature.id
  | _ => throw (IO.userError s!"compiler fixture missing {name}")

example (compiled : Compiled) {cached : Cached} (selected : compiled.artifact? = some cached) :
    cached.sourceProgram = compiled.program ∧ cached.validationPlan = compiled.plan ∧ compiled.keys = cached.keys :=
  compiled.artifact_fields selected
example (compiled : Compiled) :
    SourceCompilationPlan.validateExecutablePlanEvidence compiled.program compiled.plan = .ok () := compiled.plan_validated
example {plan : Plan} (root : Root plan) :
    ∃ specialized,
      SourceCompilationPlan.exactSpecialization plan root.key = .ok specialized ∧
      root.inputTypes = specialized.function.typedBody.inputs.map (·.scheme.body) ∧
      root.resultType = specialized.function.inferredBodyType := root.source_metadata
example {raw : Workspace.RawWorkspace} {seeds : List Seed} {options : Options} {compiled : Compiled}
    (accepted : compile raw seeds options = .ok compiled) :
    checkProgram raw options.checkingFuel = .ok compiled.program := compile_checked_source accepted
example (compiled : Compiled) (empty : compiled.artifact? = none) :
    compiled.roots = [] ∧ compiled.plan.seedKeys = [] := compiled.no_artifact_empty empty

/-- Roots whose parameter or result types hold a memory array, a slice or a memref: directly, in a
tuple, a type argument, an enum's payload, an enum named in one, or a function type. -/
private def viewRootWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := "pragma solcore;\n" ++ String.intercalate "\n" [
    "enum Box { Hold(uint256[]) }",
    "enum Wrap<t> { Wrapped(t) }",
    "enum Nest { Nested(Box) }",
    "function arrayResult() returns (uint256[]) { return new uint256[](2); }",
    "function arrayParameter(xs: uint256[]) returns (Word) { return 0; }",
    "function sliceParameter(s: arraySlice<uint256[]>) returns (Word) { return 0; }",
    "function memrefParameter(r: memref<uint256>) returns (Word) { return 0; }",
    "function tupleResult() returns ((uint256[], Word)) { return (new uint256[](2), 1); }",
    "function fieldResult() returns (Box) { return .Hold(new uint256[](2)); }",
    "function argumentResult() returns (Wrap<uint256[]>) { return .Wrapped(new uint256[](2)); }",
    "function nestedResult() returns (Nest) { return .Nested(.Hold(new uint256[](2))); }",
    "function functionResult() returns (function(uint256[]) returns (Word)) { return lam(xs: uint256[]) { return 0; }; }",
    "function wrapper(n: uint256) returns (uint256) { let a: uint256[] = new uint256[](n); return a.length(); }",
    "function wordWrap() returns (Wrap<Word>) { return .Wrapped(1); }",
    "function grow(n: uint256) returns (uint256[]) { return new uint256[](n); }",
    "function total(xs: uint256[]) returns (uint256) { return xs.length(); }",
    "function viaHandles(n: uint256) returns (uint256) { return total(grow(n)); }"
  ]}] }

/-- Issue the named handle of a declaration and call it with one argument. -/
private def callNamed {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (id : Resolved.DeclarationId) (argument : SourceCorePublicValues.Value) :
    IO (Except SourceCoreIndexedSession.Error (SourceCoreExecution.Outcome artifact)) := do
  let issued ← match ← session.named ⟨id, []⟩ with
    | .ok issued => pure issued
    | .error error => throw (IO.userError s!"named issuance refused: {reprStr error}")
  match issued.value with
  | .function handle => issued.session.invokePacked handle argument {executionFuel := 300000}
  | _ => throw (IO.userError "named issuance gave no handle")

/-- A root's signature takes no array, slice or memref anywhere (the memory arrays note, decision 5):
the compiler rejects each such root, and compiles word roots over arrays and enums of words. -/
private def testViewRoots : IO Unit := do
  let program ← get "view root checking" (checkProgram viewRootWorkspace)
  for name in ["arrayResult", "arrayParameter", "sliceParameter", "memrefParameter", "tupleResult",
      "fieldResult", "argumentResult", "nestedResult", "functionResult"] do
    let id ← declaration program name
    match compileChecked program [Seed.declaration id] options with
    | .error (.rootWithoutPublicValue _ _) => pure ()
    | other => throw (IO.userError s!"a root holding a view was not rejected: {name}, compiled {other.toOption.isSome}")
  for name in ["wrapper", "wordWrap"] do
    let id ← declaration program name
    let compiled ← get s!"word root {name}" (compileChecked program [Seed.declaration id] options)
    require (compiled.rootCount == 1) s!"word root {name} lost its root"
  -- The session's roots keep the same check, for a compilation that did not pass the compiler's.
  let arrayResult ← declaration program "arrayResult"
  let request ← get "array root request" (SourceProgramExecution.resolveSeed program (Seed.declaration arrayResult))
  let plan ← match SourceSpecializationWorklist.run program [request] 256 with
    | .ok (.complete plan) => pure plan
    | _ => throw (IO.userError "array root plan missing")
  let cached ← get "array root compilation" (SourceCoreUnifiedCompilation.prepare program plan 1000)
  match SourceCoreIndexedSession.Recipe.prepare cached with
  | .error { code := .rootWithoutPublicValue _ _, .. } => pure ()
  | other => throw (IO.userError s!"a session root holding a view was not rejected: prepared {other.toOption.isSome}")
  -- A handle whose type holds a view is issued, but the session does not call it.
  let viaHandles ← declaration program "viaHandles"
  let compiled ← get "word root over handles" (compileChecked program [Seed.declaration viaHandles] options)
  let entry ← Tests.SourceCompilerFeatureSupport.fromCompiled compiled
  let session ← Tests.SourceCompilerFeatureSupport.boot (← entry.execution.open)
  for name in ["grow", "total"] do
    match ← callNamed session (← declaration program name) (.word (w 3)) with
    | .error { code := .handleWithoutPublicValue _, .. } => pure ()
    | _ => throw (IO.userError s!"a handle holding a view was called: {name}")
  match ← callNamed session viaHandles (.word (w 3)) with
  | .ok (.succeeded completion) => require (completion.value == .word (w 3)) "the word handle over arrays changed its result"
  | _ => throw (IO.userError "the word handle over arrays failed")
  IO.println "ROOT_PUBLIC_TYPES_PASS: roots holding a memory array, a slice or a memref, through tuples, type arguments, enum payloads and function types, rejected by the compiler and by the session's roots, and handles holding one not called; word roots and handles over arrays run"

def run : IO Unit := do
  testViewRoots
  let program ← get "single Core checking" (checkProgram workspace)
  let identity ← declaration program "identity"
  let mapping ← declaration program "mappingEcho"
  let capture ← declaration program "capture"
  let seeds := [Seed.declaration mapping, Seed.declaration identity [.word],
    Seed.declaration capture, Seed.declaration identity [.word]]
  let compiled ← get "single Core compilation" (compileChecked program seeds options)
  let cached ← match compiled.artifact? with
    | some cached => pure cached | none => throw (IO.userError "nonempty roots have no cached code")
  require (compiled.rootCount == 4) "ordered roots were deduplicated"
  require (compiled.roots.map (·.seed) == seeds) "source root order changed"
  require (compiled.keys[1]? == compiled.keys[3]?) "duplicate root changed canonical specialization"
  let roots := compiled.roots
  require (roots.map (·.inputTypes) == [[.mapping .word .word], [.word], [.word], [.word]]) "public input metadata changed"
  require (roots.map (·.resultType) == [.mapping .word .word, .word, .function .word .word, .word]) "public result metadata changed"
  let raw : SourceTypedRuntime.Value := .mapping (.comptime .word) (.comptime .word)
    [(.word (w 1), .word (w 7)), (.word (w 1), .word (w 9))]
  let mappingKey ← match compiled.keys[0]? with
    | some key => pure key | none => throw (IO.userError "mapping root missing")
  let mapped ← get "cached raw mapping" (cached.run mappingKey [raw] 500 300000)
  match mapped.observation with
  | .done value _ => require (reprStr value == reprStr raw) "one compiler lost raw mapping metadata or duplicates"
  | other => throw (IO.userError s!"cached mapping failed: {reprStr other}")
  let identityKey ← match compiled.keys[1]? with
    | some key => pure key | none => throw (IO.userError "identity root missing")
  for value in [w 3, w 11] do
    let result ← get "reused cached identity" (cached.run identityKey [.word value] 500 300000)
    match result.observation with
    | .done (.word actual) _ => require (actual == value) "cached root reuse changed value"
    | other => throw (IO.userError s!"cached identity failed: {reprStr other}")
  let rawCompiled ← get "raw single Core compiler" (compile workspace seeds options)
  require (rawCompiled.keys == compiled.keys) "raw and checked compiler changed root identities"
  match compileChecked program [Seed.declaration mapping, Seed.declaration identity] options with
  | .error (.seed 1 _ (.typeArgumentArityMismatch owner 1 0)) => require (owner == identity) "wrong rejected seed"
  | other => throw (IO.userError s!"single Core compiler lost exact seed rejection: {other.toOption.isSome}")
  match compileChecked program [Seed.declaration mapping] {options with specializationBudget := 0} with
  | .error (.specializationBudgetExhausted _ _) => pure ()
  | _ => throw (IO.userError "single Core compiler lost discovery budget rejection")
  let empty ← get "empty ordered roots" (compileChecked program [] options)
  require (empty.rootCount == 0 && empty.keys.isEmpty) "empty compilation invented a root"
  require empty.artifact?.isNone "empty compilation invented callable code"

end Tests.SourceCoreCompiler
end

section
-- leanmerge: from Solcore.Test.SourceCoreFinalCatalogLateRows
/-! The final ordinary catalog also recovers the two identity rows discovered
while preparing genuine implementation methods. This reuses the existing
nested-evidence fixture and does not add another execution model. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreFinalCatalogLateRows
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory)
open Tests.SourceCoreMethodOriginEvidence

private theorem eligible {fixture signature} (row : ObservedRow fixture signature) :
    CallableIndexedOwnedPreparedOrdinaryCatalogReceipts.Eligible fixture.recipe.compiled row.named.specialized := by
  rw [row.same]
  refine ⟨row.origin, ?_, row.ordinary, row.inputsOrdinary⟩
  intro parameter replacement member
  have scalar := of_decide_eq_true (List.all_eq_true.mp row.scalarRange (parameter, replacement) member)
  rcases scalar with rfl | rfl
  · exact ⟨by simp [TypeParameterBindersWellFormed, Context.ofSignatures], .builtin .word⟩
  · exact ⟨by simp [TypeParameterBindersWellFormed, Context.ofSignatures], .builtin .bool⟩

theorem identity_packets (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    ∃ catalog : CallableIndexedOwnedPreparedOrdinaryCatalogReceipts.Catalog fixture.recipe.compiled,
      (∃ input : Input fixture.recipe.compiled, ∃ packet : Issued input,
        Inventory.HasRow packet catalog.rows ∧ input.row = observed.identityWordRow.row ∧
        input.prepared.index = observed.identityWordRow.index ∧
        input.prepared.named = observed.identityWordRow.named) ∧
      (∃ input : Input fixture.recipe.compiled, ∃ packet : Issued input,
        Inventory.HasRow packet catalog.rows ∧ input.row = observed.identityBoolRow.row ∧
        input.prepared.index = observed.identityBoolRow.index ∧
        input.prepared.named = observed.identityBoolRow.named) := by
  obtain ⟨catalog⟩ := CallableIndexedOwnedPreparedOrdinaryCatalog.of_compiled
    fixture.recipe.compiled fixture.source_wellFormed
  refine ⟨catalog, ?_, ?_⟩
  · obtain ⟨input, packet, retained, same, slot, named⟩ :=
      catalog.packet_at observed.identityWordRow.cached (eligible observed.identityWordRow)
    exact ⟨input, packet, retained, same.trans observed.identityWordRow.same, slot, named⟩
  · obtain ⟨input, packet, retained, same, slot, named⟩ :=
      catalog.packet_at observed.identityBoolRow.cached (eligible observed.identityBoolRow)
    exact ⟨input, packet, retained, same.trans observed.identityBoolRow.same, slot, named⟩

def runLateRows : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  have _packets := identity_packets fixture observed
  let early := fixture.recipe.compiled.validationPlan.specializations
  unless !(early.any (· == observed.identityWordRow.row)) &&
      !(early.any (· == observed.identityBoolRow.row)) do
    throw (IO.userError "identity rows were already in the validation plan")
  IO.println "FINAL_CATALOG_LATE_ROWS_PASS: both method-discovered identity rows are issued from the final cache"

end Tests.SourceCoreFinalCatalogLateRows
end

section
-- leanmerge: from Solcore.Test.SourceCoreGroupedTuple
/-! Grouped tuple regressions cross the parser, checker and specialization
boundary. Both the public session and the internal prepared body execute Core and
preserve transparent tuple groups, pattern binding and evaluation order. -/

set_option autoImplicit false

namespace Tests.SourceCoreGroupedTuple

open Solcore Solcore.Frontend Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def w (value : Nat) : Core.Word := Core.Word.ofNatModulo value

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [],
  mainSources := [{path := "main.solc", content := "pragma solcore;\n" ++ String.intercalate "\n" [
    "function plain(left: Word, right: Word) returns (Word) { match ((left, right)) { case (x, y) { return x; } default { return 99; } } }",
    "function grouped(left: Word, right: Word) returns (Word) { match ((left, right)) { case ((x, y)) { return x; } default { return 99; } } }",
    "function deep(left: Word, right: Word) returns (Word) { match ((left, right)) { case ((((x, y)))) { return x; } default { return 99; } } }",
    "function nested(left: Word, right: Word) returns (Word) { match ((left, (true, right))) { case (((x, (flag, y)))) { return flag ? x + y : 0; } default { return 99; } } }",
    "function three(left: Word, right: Word) returns (Word) { match ((left, true, right)) { case (((x, flag, y))) { return flag ? x + y : 0; } default { return 99; } } }",
    "function tripleEffects(left: Word, right: Word) returns (Word) { let count: Word = 0; let next = lam() -> Word { count += 1; return count; }; match ((next(), next(), next())) { case (x, y, z) { return x + y + z + count; } default { return 99; } } }",
    "function unitValue(value: Unit) returns (Word) { match (value) { case ((())) { return 7; } default { return 99; } } }",
    "function chooseArm(left: Word, right: Word) returns (Word) { match ((left, right)) { case ((0, y)) { return y; } case (((x, y))) { return x; } default { return 99; } } }",
    "function effects(left: Word, right: Word) returns (Word) { let count: Word = 0;",
    " match ((lam() -> (Word, Word) { count += 1; return (left, right); })()) {",
    " case (((x, y))) { count += x; } default { count += 99; } } return count; }"
  ]}]
}

private def coreEntry (program : CheckedProgram) (name : String) : IO SourceCorePlanCatalog.Prepared := do
  let signature ← match program.signatures.functions.filter (·.name == name) with
    | [signature] => pure signature
    | _ => throw (IO.userError s!"grouped tuple root missing: {name}")
  let plan ← match SourceSpecializationWorklist.run program
      [{declaration := signature.id, parameterSubstitution := []}] 256 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"grouped tuple plan failed: {reprStr result}")
  match SourceCorePlanCatalog.prepare program plan 256 with
  | .ok prepared => pure prepared
  | .error error => throw (IO.userError s!"grouped tuple Core compilation failed: {reprStr error}")

private def test (program : CheckedProgram) (name : String) (inputs : List Core.Value)
    (sourceInputs : List SourceCoreExecution.Value) (expected : Nat) : IO Unit := do
  let prepared ← coreEntry program name
  let entry ← match prepared.program.entries with
    | [entry] => pure entry
    | _ => throw (IO.userError "grouped tuple Core entry count changed")
  for _ in [0, 1] do
    match entry.run inputs 32768 with
    | .ok result => match result.observation with
        | .succeeded (.word actual) _ => assertTrue (actual == w expected) s!"{name} Core tuple result changed"
        | result => throw (IO.userError s!"{name} Core tuple run failed: {reprStr result}")
    | .error error => throw (IO.userError s!"{name} Core tuple input failed: {reprStr error}")
  let compiled ← SourceCompilerFeatureSupport.compileNamed program name
  assertTrue ((← compiled.run sourceInputs) == .word (w expected)) s!"{name} public tuple grouping changed"
  compiled.checkResume sourceInputs (.word (w expected)) 0
  match entry.run inputs 0 with
  | .ok result => match result.checkpoint? with
      | some checkpoint => match (checkpoint.resume 32768).observation with
          | .succeeded (.word actual) _ => assertTrue (actual == w expected) s!"{name} tuple resume changed the result"
          | result => throw (IO.userError s!"{name} tuple resume failed: {reprStr result}")
      | none => throw (IO.userError "grouped tuple zero fuel did not suspend")
  | .error error => throw (IO.userError s!"{name} tuple checkpoint input failed: {reprStr error}")

def run : IO Unit := do
  let program ← match checkProgram workspace 4096 with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"grouped tuple source rejected: {reprStr error}")
  let signature ← match program.signatures.functions.filter (·.name == "grouped") with
    | [signature] => pure signature
    | _ => throw (IO.userError "grouped tuple signature missing")
  let function ← match program.functions.filter (fun function => decide (function.declaration = signature.id)) with
    | [function] => pure function
    | _ => throw (IO.userError "grouped tuple checked body missing")
  assertTrue (function.typedBody.nodes.any fun
    | .statement node => match node.form with
        | .matchWith resolution => resolution.cases.any fun arm => match arm.pattern.source with
            | .group _ (.tuple _ 2) => true
            | _ => false
        | _ => false
    | _ => false) "regression did not retain the actual grouped tuple source"
  -- Closures capture by value: each `next()` starts again from `count = 0` and
  -- returns 1, and no closure assignment reaches the enclosing `count`.
  for (name, expected) in [("plain", 7), ("grouped", 7), ("deep", 7), ("nested", 15), ("three", 15), ("tripleEffects", 3), ("chooseArm", 7), ("effects", 7)] do
    test program name [.word (w 7), .word (w 8)] [.word (w 7), .word (w 8)] expected
  test program "chooseArm" [.word (w 0), .word (w 8)] [.word (w 0), .word (w 8)] 8
  test program "unitValue" [.unit] [.unit] 7
  IO.println "source Core grouped tuple patterns GREEN"

end Tests.SourceCoreGroupedTuple
end

section
-- leanmerge: from Solcore.Test.SourceCoreLambdaTemplates
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreLambdaTemplates.Inventory.mk
#check_failure Solcore.Frontend.SourceCoreLambdaTemplates.Receipt.mk
#check_failure Solcore.Frontend.SourceCoreLambdaTemplates.Compiled.mk
#check_failure Solcore.Frontend.SourceCoreLambdaTemplates.Authenticated.mk
#check_failure Solcore.Frontend.SourceCoreLambdaTemplates.Export.mk
#check_failure fun (receipt : Solcore.Frontend.SourceCoreLambdaTemplates.Receipt) => { receipt with body := Solcore.Core.Expr.unit }

/-! Actual compiler manifests authenticate source lambda templates after
installation and administrative weakening. Native code/type preservation,
by-value capture (a manifest references the snapshot copies made when its
lambda is created, and each call starts again from them), scope-free and
zero-parameter closures, unused principals, polymorphic bundles, tampered
descriptors/code and typed suspension are tested. Source closure export and
dynamic ancestry remain separate ledger boundaries. -/
set_option autoImplicit false
namespace Tests.SourceCoreLambdaTemplates
open Solcore Solcore.Frontend SourceInference
open SourceCoreLambdaTemplates

private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def w (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := "pragma solcore;\n" ++ String.intercalate "\n" [
    "type F = function(Word) returns (Word);",
    "function maker(value: Word) returns (F) { return lam(delta: Word) -> Word { value = value + delta; return value; }; }",
    "function zero() returns (function() returns (Word)) { return lam() -> Word { return 7; }; }",
    "function unused(value: Word) returns (Word) { let ignored = lam(item) { return item; }; return value; }",
    "function poly(flag: Bool) returns (Word, Bool) { let f = lam(item) { return item; }; return (f(1), f(flag)); }",
    "function loop(value: Word) returns (F) { let f: F; while (true) { f = lam(delta: Word) -> Word { value = value + delta; return value; }; break; } return f; }",
    "function nestedPoly(flag: Bool) returns (Word, Word) { let outer = lam(value) { let inner = lam(item) { return item; }; return inner(1); }; let one: Word = 1; return (outer(one), outer(flag)); }"
  ]}] }
private def key (program : CheckedProgram) (name : String) : IO Key := do
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError s!"lambda template fixture missing: {name}")
private def artifact (program : CheckedProgram) (names : List String) : IO SourceCoreCompatibleFunctions.Automatic := do
  let keys ← names.mapM (key program)
  let plan ← match SourceSpecializationWorklist.run program (keys.map (fun key => ⟨key.declaration, []⟩)) 128 with
    | .ok (.complete plan) => pure plan
    | other => throw (IO.userError s!"lambda template plan failed: {reprStr other}")
  match SourceCoreCompatibleFunctions.prepare program plan 256 with
  | .ok artifact => pure artifact
  | .error error => throw (IO.userError s!"lambda template artifact failed: {reprStr error}")

example {definitions : Core.DataEnvironment} {context : Core.Context} {parameter result capturesType : Core.Ty}
    {captures body : Core.Expr} (descriptor : Core.Word)
    (captured : Core.HasType context captures capturesType definitions)
    (typed : Core.HasType (parameter :: context) body result definitions) :
    Core.HasType (parameter :: context) (manifestBody descriptor [] captures body) result definitions :=
  manifestBody_hasType descriptor (by simp) captured typed

example {environment : Core.Environment} {initial final : Core.Store} {captures body : Core.Expr}
    {captureValue value : Core.Value} (descriptor : Core.Word)
    (captureEval : Core.Evaluates environment initial (captures.weakenAt 0) captureValue initial)
    (bodyEval : Core.Evaluates environment initial body value final) :
    ∃ value' final', Core.Evaluates environment initial (manifestBody descriptor [] captures body) value' final' ∧
      Core.ValuesRelated value value' ∧ Core.StoresRelated final final' :=
  manifestBody_related descriptor captureEval bodyEval

private structure Ready (checked : Checked) where
  inventory : Inventory checked
  compiled : Compiled inventory (SourceCoreCompatibleFunctions.representation (.initial checked) 256) 256
private def ready {checked : Checked} (base : Base checked) : IO (Ready checked) := do
  let inventory ← match SourceCoreLambdaTemplates.prepare base with
    | .ok inventory => pure inventory | .error error => throw (IO.userError s!"lambda inventory failed: {reprStr error}")
  let compiled ← match SourceCoreLambdaTemplates.compile inventory (SourceCoreCompatibleFunctions.representation (.initial checked) 256) 256 with
    | .ok compiled => pure compiled | .error error => throw (IO.userError s!"lambda compiler/scanner failed: {reprStr error}")
  pure ⟨inventory, compiled⟩

private def native {checked : Checked} (ready : Ready checked) (owner : Key) (arguments : SourceCoreBasic.LoweredExpr) :
    IO (SourceCoreGeneralEntry.NativeEntry checked.catalog.definitions) := do
  let base := ready.inventory.base
  let function ← match base.functions.find? (fun function => decide (function.signature.key = owner)) with
    | some function => pure function | none => throw (IO.userError "lambda compiled root missing")
  let body ← match SourceCoreGeneralFunctions.assembleCall base.globals base.functions ready.compiled.compilation.closures owner arguments with
    | .ok body => pure body | .error error => throw (IO.userError s!"lambda native assembly failed: {reprStr error}")
  match SourceCoreGeneralEntry.NativeEntry.compile checked.catalog.definitions [] function.signature.resultType body with
  | .ok native => pure native | .error error => throw (IO.userError s!"lambda manifest lost Core typing: {reprStr error}")

private def resumed {definitions : Core.DataEnvironment} (native : SourceCoreGeneralEntry.NativeEntry definitions)
    (fuel : Nat) : IO (SourceCoreGeneralEntry.Result definitions native.resultType) := do
  let result ← match native.run [] fuel with
    | .ok result => pure result | .error error => throw (IO.userError s!"lambda manifest native invocation failed: {reprStr error}")
  match result.checkpoint? with
  | some suspended => pure (suspended.resume 150000)
  | none => pure result

/-- A different descriptor remains Core-typed; source ownership must reject it. -/
private def retag (value : Core.Value) (descriptor : Core.Word) : Core.Value :=
  match value with
  | .pair tagged _ => .pair tagged (.word descriptor)
  | other => other

private theorem retag_typed {definitions : Core.DataEnvironment} {world : Core.StoreTyping}
    {value : Core.Value} {parameter result : Core.Ty} (descriptor : Core.Word)
    (typed : Core.RuntimeValueHasType world value (Core.CallableContract.functionType parameter result) definitions) :
    Core.RuntimeValueHasType world (retag value descriptor) (Core.CallableContract.functionType parameter result) definitions := by
  cases typed with
  | pair tagged _ => exact .pair tagged .word

/-- Replacing native lambda code with a constant keeps its type and captures. -/
private def replaceBody (value : Core.Value) : Core.Value :=
  match value with
  | .pair (.pair identity (.closure parameter result _ environment)) descriptor =>
      .pair (.pair identity (.closure parameter result
        (Core.LanguageResult.success (.word (w 999))) environment)) descriptor
  | other => other

private theorem replaceBody_typed {definitions : Core.DataEnvironment} {world : Core.StoreTyping}
    {value : Core.Value} {parameter : Core.Ty}
    (typed : Core.RuntimeValueHasType world value (Core.CallableContract.functionType parameter .word) definitions) :
    Core.RuntimeValueHasType world (replaceBody value) (Core.CallableContract.functionType parameter .word) definitions := by
  cases typed with
  | pair tagged descriptor =>
    cases tagged with
    | pair identity function =>
      cases function with
      | closure environment _ =>
        exact .pair (.pair identity (.closure environment (.inRight .word .word))) descriptor

/-- Even a behaviorally transparent, typed edit invalidates cached global code. -/
private def replaceGlobal (value : Core.Value) : Core.Value :=
  match value with
  | .inRight .unit (.closure parameter result body environment) =>
      .inRight .unit (.closure parameter result (.letE .unit (body.weakenAt 0)) environment)
  | other => other

private theorem replaceGlobal_typed {definitions : Core.DataEnvironment} {world : Core.StoreTyping}
    {value : Core.Value} {parameter result : Core.Ty}
    (typed : Core.RuntimeValueHasType world value
      (Core.OptionalCell.cellType (.function parameter result)) definitions) :
    Core.RuntimeValueHasType world (replaceGlobal value)
      (Core.OptionalCell.cellType (.function parameter result)) definitions := by
  cases typed with
  | inLeft payload => exact .inLeft payload
  | inRight function =>
    cases function with
    | closure environment body =>
      exact .inRight (.closure environment (.letE .unit
        (by simpa only [Core.Context.insertAt] using body.weakenAt (inserted := .unit) 0)))

private def callTwice {definitions : Core.DataEnvironment} {world : Core.StoreTyping} {store : Core.Store}
    (stored : Core.RuntimeStoreHasTypes world store definitions) (value : Core.Value)
    (typed : Core.RuntimeValueHasType world value (Core.CallableContract.functionType .word .word) definitions)
    (captureLocations : List Nat) : IO Unit := do
  let call := fun n => Core.Expr.apply (.second (.first (.var 0))) (.word (w n))
  let expression := Core.LocalSequence.pair .word .word (call 1) (call 2)
  have body : Core.HasType [Core.CallableContract.functionType .word .word] expression
      (Core.LanguageResult.resultType (.product .word .word)) definitions :=
    Core.LocalSequence.pair_hasType .word .word
      (.apply (.second (.first (.var rfl))) .word)
      (.apply (.second (.first (.var rfl))) .word)
  let checkpoint : SourceCoreGeneralEntry.Checkpoint definitions (.product .word .word) := {
    state := Core.State.initial expression [value] store
    typed := .eval stored (.cons typed .nil) body .nil
  }
  for fuel in [0, 11, 150000] do
    let first := checkpoint.resume fuel
    let completed := match first.checkpoint? with
      | some next => next.resume 150000 | none => first
    match completed.observation with
    | .succeeded (.pair (.word left) (.word right)) final =>
      -- Each call starts again from the creation-time `value = 3`.
      assertTrue (left == w 4 && right == w 5) "lambda calls did not restart from their creation-time capture"
      -- Every capture of these lambdas is copied: each call allocates one plain
      -- cell per capture and one for its parameter.
      assertTrue (final.length == store.length + 2 * (captureLocations.length + 1))
        "manifest allocated an extra heap cell during invocation"
      assertTrue (captureLocations.all (fun location => final[location]? == store[location]?))
        "lambda call wrote its snapshot cell"
      assertTrue (captureLocations.any (fun location => final[location]? == some (.inRight .unit (.word (w 3)))))
        "lambda manifest lost the creation-time source capture"
    | other => throw (IO.userError s!"typed lambda reuse/resume failed: {reprStr other}")

private def checkClosure {checked : Checked} (ready : Ready checked) (owner : Key) (parameter : Core.Ty)
    (arguments : SourceCoreBasic.LoweredExpr) : IO Unit := do
  let native ← native ready owner arguments
  if same : native.resultType = Core.CallableContract.functionType parameter .word then
    for fuel in [0, 7, 37, 150000] do
      let result ← resumed native fuel
      match success : result.observation with
      | .succeeded value store =>
        have typed : Core.RuntimeStoreHasTypes (store.map Core.Value.type) store checked.catalog.definitions ∧
            Core.RuntimeValueHasType (store.map Core.Value.type) value (Core.CallableContract.functionType parameter .word) checked.catalog.definitions := by
          obtain ⟨world, stored, typed⟩ := result.success_typed success
          have equal := stored.world_eq
          subst world
          exact ⟨stored, by simpa only [same] using typed⟩
        let exported ← match authenticateCompiled ready.compiled typed.1 value parameter .word typed.2 with
          | .ok exported => pure exported | .error error => throw (IO.userError s!"lambda exact typed capture authentication failed: {reprStr error}")
        assertTrue (exported.closure.captures.locations.length == exported.template.scope.length)
          "lambda template dropped a lexical source reference"
        assertTrue (exported.template.lambda.owner == owner) "lambda template claimed another source owner"
        match authenticateCompiled ready.compiled typed.1 (retag value (w 999999)) parameter .word
            (retag_typed _ typed.2) with
        | .error .closureMismatch => pure ()
        | _ => throw (IO.userError "same-typed foreign descriptor was authenticated")
        match authenticateCompiled ready.compiled typed.1 (replaceBody value) parameter .word
            (replaceBody_typed typed.2) with
        | .error .closureMismatch => pure ()
        | _ => throw (IO.userError "same-typed modified closure body was authenticated")
        if fuel == 150000 then
          if parameterWord : parameter = .word then
            callTwice typed.1 value (by simpa only [parameterWord] using typed.2) exported.closure.captures.locations
          let global ← match ready.inventory.base.globals.head? with
            | some global => pure global | none => throw (IO.userError "lambda fixture has no globals")
          let location := ready.inventory.base.globals.length - 1
          let type := Core.OptionalCell.cellType global.functionType
          if found : (store.map Core.Value.type)[location]? = some type then
            match lookup : store.read? location with
            | none => throw (IO.userError "typed global slot unexpectedly absent")
            | some oldValue =>
              have oldTyped : Core.RuntimeValueHasType (store.map Core.Value.type) oldValue type checked.catalog.definitions := by
                obtain ⟨other, otherLookup, otherTyped⟩ := typed.1.read found
                rw [lookup] at otherLookup
                cases otherLookup
                exact otherTyped
              let changed := replaceGlobal oldValue
              have changedTyped : Core.RuntimeValueHasType (store.map Core.Value.type) changed type checked.catalog.definitions :=
                replaceGlobal_typed oldTyped
              match written : store.write? location changed with
              | none => throw (IO.userError "typed global slot unexpectedly outside heap")
              | some changedStore =>
                have changedStored := typed.1.write found changedTyped written
                match authenticateCompiled ready.compiled changedStored value parameter .word typed.2 with
                | .error (.globalSlotMismatch _) => pure ()
                | _ => throw (IO.userError "same-typed changed global code was authenticated")
          else throw (IO.userError "actual installed global slot had another type")
      | other => throw (IO.userError s!"lambda manifest run did not finish: {reprStr other}")
  else throw (IO.userError "lambda test source result projection changed")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program | .error error => throw (IO.userError s!"lambda template source rejected: {reprStr error}")
  let artifact ← artifact program ["maker", "zero", "unused", "poly", "loop", "nestedPoly"]
  let ready ← ready artifact.prepared
  assertTrue (ready.inventory.unusedPrincipals.any (fun binding => binding.binder.name == "ignored"))
    "unused generic principal falsely required a native lambda emission"
  let maker ← key program "maker"
  let zero ← key program "zero"
  let loop ← key program "loop"
  let poly ← key program "poly"
  let nestedPoly ← key program "nestedPoly"
  assertTrue (ready.compiled.templates.length == 9) "source templates omitted lambda/bundle candidate or included a helper lambda"
  let monoTemplate ← match ready.compiled.templates.find? (fun template => decide (template.lambda.owner = maker)) with
    | some template => pure template | none => throw (IO.userError "actual source lambda manifest not found")
  assertTrue (monoTemplate.scope.length == 1 && monoTemplate.references.length == 1) "source scalar capture omitted"
  let zeroTemplate ← match ready.compiled.templates.find? (fun template => decide (template.lambda.owner = zero)) with
    | some template => pure template | none => throw (IO.userError "zero-parameter manifest missing")
  assertTrue (zeroTemplate.scope.isEmpty && zeroTemplate.references.isEmpty && zeroTemplate.parameterType == .unit)
    "scope-free or zero-parameter lambda gained captures"
  let bundle := ready.compiled.templates.filter (fun template => decide (template.lambda.owner = poly))
  assertTrue (bundle.length == 2 && bundle.all (fun template => !template.lambda.active.isEmpty))
    "principal polymorphic bundle was confused with a monomorphic emitted closure"
  let loopTemplate ← match ready.compiled.templates.find? (fun template => decide (template.lambda.owner = loop)) with
    | some template => pure template | none => throw (IO.userError "lambda nested in loop lost manifest")
  -- A manifest references the snapshot copies made right before its lambda.
  -- `loop` copies `f` before `value`, so `f`'s copy is the deeper one; loop and
  -- install weakening reach the reads of those copies, not the manifest.
  assertTrue (monoTemplate.references == [0] && loopTemplate.references == [1, 0])
    "manifest references did not select the lambda's snapshot copies"
  checkClosure ready maker .word ⟨.word, Core.LanguageResult.success (.word (w 3))⟩
  checkClosure ready zero .unit ⟨.unit, Core.LanguageResult.success .unit⟩
  checkClosure ready loop .word ⟨.word, Core.LanguageResult.success (.word (w 3))⟩
  let nested := ready.compiled.templates.filter (fun template => decide (template.lambda.owner = nestedPoly))
  assertTrue (nested.length == 4 && nested.all (fun template => !template.lambda.active.isEmpty))
    "nested polymorphic templates lost their full selected context"
  assertTrue ((nested.map (fun template => template.lambda.descriptor)).eraseDups.length == 4)
    "nested selected instances collided in the callable descriptor table"
  let nestedNative ← native ready nestedPoly ⟨.bool, Core.LanguageResult.success (.bool true)⟩
  for fuel in [0, 23, 150000] do
    let nestedResult ← resumed nestedNative fuel
    match nestedResult.observation with
    | .succeeded (.pair (.word left) (.word right)) _ =>
      assertTrue (left == w 1 && right == w 1) "nested manifested bundle changed source-call results"
    | other => throw (IO.userError s!"nested manifested bundle failed: {reprStr other}")
  let .pair tagged _ := monoTemplate.carrier | throw (IO.userError "lambda carrier shape changed")
  match decode ready.inventory (.pair tagged (.word (w 999999))) with
  | .error (.descriptorMismatch _ _) => pure () | _ => throw (IO.userError "lambda descriptor tamper accepted")
  let .pair (.pair identity (.lambda parameter result body)) descriptor := monoTemplate.carrier
    | throw (IO.userError "lambda template shape changed")
  let .letE metadata _ := body | throw (IO.userError "lambda manifest body missing")
  match decode ready.inventory (.pair (.pair identity (.lambda parameter result (.letE metadata .unit))) descriptor) with
  | .ok structural =>
    assertTrue (structural.body != monoTemplate.body) "structural decode accidentally authenticated compiler emission history"
  | .error _ => throw (IO.userError "syntactic scanner should distinguish shape from actual cached emission ownership")
  IO.println "lambda manifests/installed templates, typed tamper/capture auth, by-value captures, nested bundles and resume GREEN"
end Tests.SourceCoreLambdaTemplates
end

section
-- leanmerge: from Solcore.Test.SourceCoreMappingWithDefault
/-! Execute the compatibility carrier's ordinary Core code. These tests cover
transported defaults, first duplicate selection, retained raw metadata,
missing-default tokens, effects and native suspension/resume. -/

set_option autoImplicit false

namespace Tests.SourceCoreMappingWithDefault
open Solcore Solcore.Core

private def word (value : Nat) : Word := Word.ofNatModulo value
private def layout : OrderedMapping.Layout := ⟨.word, .word, ⟨0⟩⟩
private def definitions : DataEnvironment := [layout.definition]
private def comparator : Expr :=
  .lambda (.product .word .word) .bool (.binary .wordEq (.first (.var 0)) (.second (.var 0)))
private def stored : Expr :=
  OrderedMapping.cons layout (.word (word 3)) (.word (word 9))
    (OrderedMapping.cons layout (.word (word 3)) (.word (word 100)) (OrderedMapping.empty layout))
private def literal (fallback : Option Nat) : Expr :=
  Frontend.SourceCoreMappingWithDefault.pack (.word (word 41))
    (match fallback with
      | none => .inLeft .word .unit
      | some value => .inRight .unit (.word (word value))) stored
private def program (type : Ty) (body : Expr) : Program := ⟨type, body, definitions⟩
private def entries : OrderedMapping.Entries :=
  [(.word (word 3), .word (word 9)), (.word (word 3), .word (word 100))]
private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def completes (program : Program) (expected : Value) : IO Store := do
  assertTrue program.check "mapping default carrier failed Core checking"
  match program.runStateful 10000 with
  | .done value store =>
      assertTrue (value == expected) s!"mapping default result changed: {reprStr value}"
      pure store
  | other => throw (IO.userError s!"mapping default run did not complete: {reprStr other}")

example : layout.Registered definitions := ⟨.word, .word, rfl⟩

/-- The actual wrapper is typed using the registered ordered mapping helper. -/
example : HasType [] (Frontend.SourceCoreMappingWithDefault.lookup layout (word 1000) comparator (literal (some 77)) (.word (word 8)))
    (LanguageResult.resultType .word) definitions := by
  apply Frontend.SourceCoreMappingWithDefault.lookup_hasType (word 1000) ⟨.word, .word, rfl⟩
  · exact .lambda (.product .word .word) .bool (.binary (.first (.var rfl)) (.second (.var rfl)))
  · exact Frontend.SourceCoreMappingWithDefault.pack_hasType .word (.inRight .unit .word)
      (OrderedMapping.cons_hasType ⟨.word, .word, rfl⟩ .word .word
        (OrderedMapping.cons_hasType ⟨.word, .word, rfl⟩ .word .word
          (OrderedMapping.empty_hasType ⟨.word, .word, rfl⟩ [])))
  · exact .word

def run : IO Unit := do
  let present := program (LanguageResult.resultType .word)
    (Frontend.SourceCoreMappingWithDefault.lookup layout (word 1000) comparator (literal (some 77)) (.word (word 3)))
  let presentStore ← completes present (.inRight .word (.word (word 9)))
  assertTrue (presentStore.length == 1) "present lookup changed helper allocation count"
  let absent := program (LanguageResult.resultType .word)
    (Frontend.SourceCoreMappingWithDefault.lookup layout (word 1000) comparator (literal (some 77)) (.word (word 8)))
  let _ ← completes absent (.inRight .word (.word (word 77)))
  let missing := program (LanguageResult.resultType .word)
    (Frontend.SourceCoreMappingWithDefault.lookup layout (word 1000) comparator (literal none) (.word (word 8)))
  let _ ← completes missing (.inLeft .word (.word (word 1041)))
  let inserted := program (LanguageResult.resultType (Frontend.SourceCoreMappingWithDefault.type layout))
    (Frontend.SourceCoreMappingWithDefault.insert layout comparator (literal (some 77)) (.word (word 3)) (.word (word 12)))
  let _ ← completes inserted (.inRight .word (Frontend.SourceCoreMappingWithDefault.value (word 41) (some (.word (word 77))) layout
    [(.word (word 3), .word (word 12)), (.word (word 3), .word (word 100))]))
  let stillDefault := program (LanguageResult.resultType .word)
    (LanguageResult.bind .word inserted.body
      (Frontend.SourceCoreMappingWithDefault.lookup layout (word 1000) (comparator.weakenAt 0) (.var 0) (.word (word 8))))
  let _ ← completes stillDefault (.inRight .word (.word (word 77)))
  let once := program (.product (LanguageResult.resultType .word) .word)
    (.letE (.newCell .word (.word Word.zero))
      (.letE (Frontend.SourceCoreMappingWithDefault.lookup layout (word 1000) comparator
        (.letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (.word (word 1))))
          (literal (some 77))) (.word (word 8)))
        (.pair (.var 0) (.loadCell (.var 1)))))
  let onceStore ← completes once (.pair (.inRight .word (.word (word 77))) (.word (word 1)))
  assertTrue (onceStore[0]? == some (.word (word 1))) "mapping expression ran more than once"
  for fuel in List.range 64 do
    match absent.runStateful fuel with
    | .outOfFuel checkpoint =>
        match runStateful 10000 checkpoint with
        | .done value _ => assertTrue (value == .inRight .word (.word (word 77))) "mapping default resume changed"
        | _ => throw (IO.userError "mapping default resume did not complete")
    | .done value _ => assertTrue (value == .inRight .word (.word (word 77))) "mapping default finite run changed"
    | .fault error _ => throw (IO.userError s!"mapping default reached a machine fault: {reprStr error}")
  assertTrue (decide (Frontend.SourceCoreMappingWithDefault.value (word 41) none layout entries =
    .pair (.word (word 41)) (.pair (.inLeft .word .unit) (OrderedMapping.encode layout entries))))
    "mapping carrier lost its raw metadata header"
  IO.println "ordinary Core mapping metadata and transported defaults GREEN"

end Tests.SourceCoreMappingWithDefault
end

section
-- leanmerge: from Solcore.Test.SourceCoreOrdinarySyntaxTable
set_option autoImplicit false
open Solcore Frontend SourceInference SourceSemantics CoreLowering

namespace Tests.SourceCoreOrdinarySyntaxTable

def run : IO Unit := do
  let fixture ← Tests.SourceCoreCanonicalFormation.compiledFixture
  let observed ← Tests.SourceCoreCanonicalFormation.observeProgram fixture
  let table := CallableIndexedOwnedPreparedOrdinarySyntaxTable.collect fixture.recipe.compiled fixture.source_wellFormed 100
  unless table.rows.length == 3 && table.rows.any (· == observed.identityRow.row) do
    throw (IO.userError "actual ordinary cache table mismatch")
  match fixture.recipe.compiled.indexed.base.functions[observed.relayRow.index]? with
  | none => throw (IO.userError "relay cache missing")
  | some named =>
    match CallableIndexedOwnedPreparedNamedScopedAdmission.admitSource fixture.recipe.compiled named named.specialized.function.typedBody
        [observed.relayShape.statement.id] .word table.rows 100 with
    | none => throw (IO.userError "actual nonempty direct table source rejected")
    | some _ => IO.println "SYNTAX_TABLE_DIRECT_PASS: actual 3-row table admitted the original relay direct call"
  let nominal ← Tests.SourceCoreConstructorCalls.checkedFixture
  unless (CallableIndexedOwnedPreparedOrdinarySyntaxTable.type? nominal.program.signatures 100 (.nominal nominal.dataType.id [])).isSome do
    throw (IO.userError "actual nominal formation rejected")
  unless (CallableIndexedOwnedPreparedOrdinarySyntaxTable.type? nominal.program.signatures 100 (.nominal nominal.dataType.id [.word])).isNone do
    throw (IO.userError "wrong nominal arity accepted")
  unless (CallableIndexedOwnedPreparedOrdinarySyntaxTable.type? nominal.program.signatures 100 (.nominal nominal.makeSignature.id [])).isNone do
    throw (IO.userError "function declaration accepted as nominal")
  unless (CallableIndexedOwnedPreparedOrdinarySyntaxTable.type? nominal.program.signatures 100 (.variable ⟨0⟩)).isNone &&
      (CallableIndexedOwnedPreparedOrdinarySyntaxTable.type? nominal.program.signatures 100 (.parameter ⟨nominal.makeSignature.id, 0⟩)).isNone &&
      (CallableIndexedOwnedPreparedOrdinarySyntaxTable.type? nominal.program.signatures 0 .word).isNone do
    throw (IO.userError "open or exhausted type accepted")
  unless (CallableIndexedOwnedPreparedOrdinarySyntaxTable.type? nominal.program.signatures 100
      (.function (.product .word .bool) (.mapping .word (.proxy .bool)))).isSome do
    throw (IO.userError "closed compound type rejected")
  let parameter : TypeSystem.TypeParameterId := ⟨nominal.makeSignature.id, 0⟩
  unless (CallableIndexedOwnedPreparedOrdinarySyntaxTable.range? nominal.program.signatures 100
      [(parameter, .word), (parameter, .nominal nominal.makeSignature.id [])]).isNone do
    throw (IO.userError "invalid later replacement in a duplicate row was ignored")
  IO.println "SYNTAX_TABLE_TYPES_PASS: nominal/compound accepted; wrong arity/nondata/open/fuel/full-range rejected"
  let late ← Tests.SourceCoreMethodOriginEvidence.compiledFixture
  let observedLate ← Tests.SourceCoreMethodOriginEvidence.observeProgram late
  let lateTable := CallableIndexedOwnedPreparedOrdinarySyntaxTable.collect late.recipe.compiled late.source_wellFormed 100
  unless lateTable.rows.any (· == observedLate.identityWordRow.row) &&
      lateTable.rows.any (· == observedLate.identityBoolRow.row) do
    throw (IO.userError "late identity rows missing from executable table")
  IO.println s!"SYNTAX_TABLE_LATE_PASS: {lateTable.rows.length} ordinary rows include both method-discovered identities"

end Tests.SourceCoreOrdinarySyntaxTable
end

section
-- leanmerge: from Solcore.Test.SourceCorePlanCatalog
#check_failure Solcore.Frontend.SourceTypedRuntime.run

set_option autoImplicit false

namespace Tests.SourceCorePlanCatalog

open Solcore Solcore.Frontend Solcore.Core
abbrev SourceValue := SourceCoreDataValues.Value

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := "pragma solcore;\n" ++ String.intercalate "\n" [
    "enum Tree<T> { Leaf(T), Pair(Tree<T>, Tree<T>) }",
    "function leaf(value: Word) returns (Tree<Word>) { return .Leaf(value); }",
    "function main(flag: Bool, value: Word) returns (Tree<Word>) { return flag ? leaf(value) : .Pair(leaf(value), leaf(value + 1)); }",
    "function recursive(count: Word, value: Tree<Word>) returns (Tree<Word>) { return count == 0 ? value : recursive(count - 1, Tree.Pair(value, value)); }",
    "function mappingValue(table: mapping(Word => Word)) returns (mapping(Word => Word)) { table[7] += 3; return table; }",
    "function proxyValue() returns (@Tree<Word>) { return @Tree<Word>; }"
  ] }]
}

private def preparedFor (program : CheckedProgram) (name : String) : IO SourceCorePlanCatalog.Prepared := do
  let signature ← match program.signatures.functions.filter (·.name == name) with
    | [signature] => pure signature
    | _ => throw (IO.userError s!"automatic catalog function missing: {name}")
  let plan ← match SourceSpecializationWorklist.run program
      [{ declaration := signature.id, parameterSubstitution := [] }] 256 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"automatic catalog specialization failed: {reprStr result}")
  match SourceCorePlanCatalog.prepare program plan 256 with
  | .ok prepared => pure prepared
  | .error error => throw (IO.userError s!"automatic catalog preparation failed: {reprStr error}")

private def execute (signatures : ProgramSignatures) (prepared : SourceCorePlanCatalog.Prepared)
    (arguments : List SourceValue) : IO SourceValue := do
  let entry ← match prepared.program.entries with
    | [entry] => pure entry
    | _ => throw (IO.userError "automatic catalog seed count changed")
  let context : SourceCoreDataValues.Context := ⟨prepared.checked, signatures⟩
  let arguments ← (entry.inputs.zip arguments).mapM fun (input, argument) => do
    match SourceCoreDataValues.encode 256 context input.sourceType argument with
    | .ok core => pure core
    | .error error => throw (IO.userError s!"source input rejected: {reprStr error}")
  match entry.run arguments 65536 with
  | .ok result => match result.observation with
      | .succeeded value _ => match SourceCoreDataValues.decode 256 context entry.sourceResultType value with
          | .ok value => pure value
          | .error error => throw (IO.userError s!"source result rejected: {reprStr error}")
      | other => throw (IO.userError s!"automatic catalog execution failed: {reprStr other}")
  | .error error => throw (IO.userError s!"automatic catalog native input rejected: {reprStr error}")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"automatic catalog source rejected: {reprStr error}")
  let tree ← match program.signatures.dataTypes.filter (·.name == "Tree") with
    | [tree] => pure tree
    | _ => throw (IO.userError "automatic Tree signature missing")
  let treeType := TypeSystem.Ty.nominal tree.id [.word]
  let substitution := tree.parameters.zip [TypeSystem.Ty.word]
  let metadata := fun index payload => SourceInference.DataConstructorInstantiation.mk
    ⟨tree.id, index⟩ substitution payload treeType
  let word := fun value => SourceCoreDataValues.Value.word (Core.Word.ofNatModulo value)
  let leaf := fun value => SourceCoreDataValues.Value.constructed (metadata 0 [.word]) [word value]
  let pair := fun left right => SourceCoreDataValues.Value.constructed (metadata 1 [treeType, treeType]) [left, right]
  let main ← preparedFor program "main"
  for _ in [0, 1] do
    assertTrue (decide ((← execute program.signatures main [.bool true, word 8]) = leaf 8))
      "automatically discovered nominal output changed"
    assertTrue (decide ((← execute program.signatures main [.bool false, word 8]) = pair (leaf 8) (leaf 9)))
      "automatically discovered recursive payload changed"
  let recursive ← preparedFor program "recursive"
  assertTrue (decide ((← execute program.signatures recursive [word 2, leaf 3]) =
    pair (pair (leaf 3) (leaf 3)) (pair (leaf 3) (leaf 3))))
    "automatic recursive catalog lost constructor identity"
  let mapping ← preparedFor program "mappingValue"
  let entries := [(word 7, word 4), (word 7, word 99), (word 2, word 6)]
  assertTrue (decide ((← execute program.signatures mapping [.mapping .word .word entries]) =
    .mapping .word .word [(word 7, word 7), (word 7, word 99), (word 2, word 6)]))
    "automatic ordered mapping changed duplicate positions"
  assertTrue (decide ((← execute program.signatures (← preparedFor program "proxyValue") []) = .proxy treeType))
    "automatic catalog lost proxy inner type"
  let context : SourceCoreDataValues.Context := ⟨recursive.checked, program.signatures⟩
  assertTrue (match SourceCoreDataValues.encode 256 context treeType
      (.constructed (metadata 0 [.word]) [.integer 3]) with | .error _ => true | _ => false)
    "source input adapter accepted a forged nominal payload"
  IO.println "source Core automatic plan catalogs GREEN"

end Tests.SourceCorePlanCatalog
end

section
-- leanmerge: from Solcore.Test.SourceCorePublicRootStartReceipt
/-! Public startup receipts preserve the actual encoder and machine state.
The source representation of encoded inputs remains an independent obligation. -/
set_option autoImplicit false
namespace Solcore.Test.SourceCorePublicRootStartReceipt
open Frontend.SourceCoreIndexedSession

abbrev actual_start := @Session.start_root_receipt
abbrev original_completion := @Checkpoint.RootStart.native_completed

theorem actual_start_heap {artifact : Artifact} (session : Session artifact)
    {key : Frontend.SourceCoreFunctions.Key} {arguments : List Frontend.SourceCorePublicValues.Value}
    {fuel : Nat} {checkpoint : Checkpoint artifact}
    (accepted : session.start key arguments fuel = .ok checkpoint) :
    checkpoint.heapSize = session.heapSize :=
  (Session.start_root_receipt session accepted).heap_size

end Solcore.Test.SourceCorePublicRootStartReceipt
end

section
-- leanmerge: from Solcore.Test.SourceCorePublicSourceOutcomes
/-! The original public sessions expose their independent Source outcomes and
retain the staged witnesses used by the existing forward fuel conclusions. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCorePublicSourceOutcomes

def run : IO Unit := do
  SourceCoreMethodOriginEvidence.SourceOutcomes.run
  SourceCoreCanonicalScoped.SourceOutcomes.run
  SourceCoreCertifiedLexicalFailure.SourceOutcomes.run
  IO.println "PUBLIC_SOURCE_OUTCOMES_PASS: actual X7 at checker1024 and1000; original scoped C6 with retained packed calls; lexical fault and subsequent/fresh identity; exact Dynamic success/fault outcomes, original heaps and forward bounds"

end Tests.SourceCorePublicSourceOutcomes
end

section
-- leanmerge: from Solcore.Test.SourceCoreRepresentationProjection
/-! Checked local instances retain their source inventory while projecting
their mapping parameter and result through the selected representation.
Callable origins, IDs and decisions still come from original source metadata. -/
set_option autoImplicit false
namespace Tests.SourceCoreRepresentationProjection
open Solcore Solcore.Frontend SourceInference

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content := "pragma solcore;\n" ++
    "function local(table: mapping(Word => Word)) returns (mapping(Word => Word)) { let f = lam(item) { return item; }; return f(table); }"}]
}

example {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {projectType : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty}
    {limits : SourceCoreStageCodebook.Limits} {firstId : Nat} {table : SourceCoreStageCodebook.Table}
    (accepted : SourceCoreStageCodebook.prepareWithProjection program plan projectType limits firstId = .ok table) :
    SourceSemantics.CoreLowering.CallEntryCertificates.AllAuthenticated plan table.entries :=
  SourceSemantics.CoreLowering.CallEntryCertificates.prepareWithProjection_authenticates accepted

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"projection fixture rejected: {reprStr error}")
  let signature ← match program.signatures.functions.filter (·.name == "local") with
    | [signature] => pure signature
    | _ => throw (IO.userError "projection root missing")
  let plan ← match SourceSpecializationWorklist.run program [⟨signature.id, []⟩] 64 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"projection discovery failed: {reprStr result}")
  let plan ← match SourceCompilationPlan.prepareExecutablePlanEvidence program plan with
    | .ok plan => pure plan
    | .error error => throw (IO.userError s!"projection plan failed: {reprStr error}")
  let discovered ← match SourceCompilationPlan.localLambdaCatalog plan with
    | .ok discovered => pure discovered
    | .error error => throw (IO.userError s!"projection local discovery failed: {reprStr error}")
  let types := (SourceCorePlanCatalog.planTypes plan ++ discovered.flatMap (fun entry =>
    SourceCorePlanCatalog.sourceTypes (entry.source.applySubstitution entry.substitution))).filter
      SourceCoreDataCatalog.closed |>.eraseDups
  let strict ← match SourceCoreDataCatalog.prepare program.signatures 256 types true with
    | .ok strict => pure strict
    | .error error => throw (IO.userError s!"strict projection failed: {reprStr error}")
  let compatible ← match SourceCoreCompatibleCatalog.prepare program.signatures 256 types with
    | .ok compatible => pure compatible
    | .error error => throw (IO.userError s!"compatible projection failed: {reprStr error}")
  let project : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty := fun type =>
    (compatible.project type).map (·.type) |>.mapError fun _ => .initializerMetadataMismatch ⟨⟨signature.id, 0⟩⟩
  let locals ← match SourceCoreLocalPolymorphism.prepareWithProjection project plan with
    | .ok locals => pure locals
    | .error error => throw (IO.userError s!"compatible local projection failed: {reprStr error}")
  let candidate ← match locals.bindings.flatMap (·.instances) with
    | [candidate] => pure candidate
    | _ => throw (IO.userError "projection local instance missing")
  let native ← match compatible.catalog.project (.mapping .word .word) with
    | .ok type => pure type
    | .error error => throw (IO.userError s!"compatible mapping projection failed: {reprStr error}")
  unless candidate.parameterType == native && candidate.resultType == native do
    throw (IO.userError "local mapping instance used another representation")
  let old ← match strict.catalog.project (.mapping .word .word) with
    | .ok type => pure type
    | .error error => throw (IO.userError s!"strict mapping projection failed: {reprStr error}")
  unless old != native do throw (IO.userError "fixture did not distinguish mapping representations")
  let strictTable ← match SourceCoreStageCodebook.prepare program plan strict with
    | .ok table => pure table
    | .error error => throw (IO.userError s!"strict codebook failed: {reprStr error}")
  let compatibleTable ← match SourceCoreStageCodebook.prepareWithProjection program plan project with
    | .ok table => pure table
    | .error error => throw (IO.userError s!"compatible codebook failed: {reprStr error}")
  unless (strictTable.entries.map (fun entry => (entry.id, entry.origin, entry.parameterCount))) ==
      (compatibleTable.entries.map (fun entry => (entry.id, entry.origin, entry.parameterCount))) do
    throw (IO.userError "representation changed callable origins or IDs")
  unless (strictTable.decisions.map (fun row => (row.caller, row.call, row.entry.id, row.argumentCount, reprStr row.answer))) ==
      (compatibleTable.decisions.map (fun row => (row.caller, row.call, row.entry.id, row.argumentCount, reprStr row.answer))) do
    throw (IO.userError "representation changed original stage decisions")
  IO.println "shared representation projection preserves local discovery and callable metadata GREEN"

end Tests.SourceCoreRepresentationProjection
end

section
-- leanmerge: from Solcore.Test.SourceCoreRootDiscovery
#check_failure Solcore.Frontend.SourceCoreRootDiscovery.CheckedEntry.mk

/-! Conventional main and exported ABI roots retain exact names and canonical
module identities without a runtime backend selection. Conflict diagnostics
are the existing Static Word profile's deterministic diagnostics. -/
set_option autoImplicit false
namespace Tests.SourceCoreRootDiscovery
open Solcore Solcore.Frontend SourceCoreRootDiscovery
private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def single (content : String) : Workspace.RawWorkspace := {
  entry := "api.solc", externalLibraries := [], mainSources := [{path := "api.solc", content := "pragma solcore;\n" ++ content}] }
private def workspace : Workspace.RawWorkspace := {
  entry := "api.solc", externalLibraries := [], mainSources := [
    {path := "api.solc", content := "pragma solcore;\n" ++ String.intercalate "\n" [
      "import {twice as doubled, recursive} from provider;",
      "function main() returns (Word) { return 17; }",
      "function local(value: Word) returns (Word) { return value + 1; }",
      "function hidden(value: Word) returns (Word) { return value; }",
      "export {doubled, local, recursive};"]},
    {path := "provider.solc", content := "pragma solcore;\n" ++ String.intercalate "\n" [
      "function twice(value: Word) returns (Word) { return value * 2; }",
      "function recursive(value: Word) returns (Word) { return value == 0 ? 31 : recursive(value - 1); }",
      "function providerOnly(value: Word) returns (Word) { return value; }",
      "export {twice, recursive, providerOnly};"]}] }

example {raw : Workspace.RawWorkspace} {fuel : Nat} (entry : CheckedEntry raw fuel) :
    checkProgram raw fuel = .ok entry.program := entry.source_checked

def run : IO Unit := do
  let checked ← get "entry discovery" (checkEntry workspace)
  let request ← get "conventional main resolution" (SourceProgramExecution.resolveSeed checked.program checked.seed)
  require (request.declaration.moduleId == checked.moduleId) "main resolution changed the entry module"
  let roots ← get "ABI discovery" (discoverStaticWordRoots checked.program checked.moduleId)
  require (roots.map (·.metadata.name.text) == ["local", "doubled", "recursive"])
    s!"ABI alias/order/visibility changed: {reprStr (roots.map (·.metadata.name.text))}"
  let compiled ← get "one ABI Core compilation"
    (SourceCoreCompiler.compileChecked checked.program (roots.map (·.seed)) {specializationBudget := 128, compilationFuel := 1000})
  require (compiled.rootCount == 3 && compiled.roots.map (·.inputTypes) == [[.word], [.word], [.word]]) "ABI roots lost source metadata"
  let missing ← get "missing main check" (checkEntry (single "function helper() returns (Word) { return 0; }"))
  match SourceProgramExecution.resolveSeed missing.program missing.seed with
  | .error (.unknownName moduleId "main") => require (moduleId == missing.moduleId) "missing main lost canonical module"
  | _ => throw (IO.userError "missing main was accepted")
  let invalid ← get "invalid ABI check" (checkEntry (single "function bad(value: Bool) returns (Word) { return value ? 1 : 0; } export {bad};"))
  match discoverStaticWordRoots invalid.program invalid.moduleId with
  | .error (.unsupportedParameters _ "bad" [.bool] [false]) => pure ()
  | _ => throw (IO.userError "unsupported ABI parameter was skipped")
  let duplicate ← get "duplicate ABI check" (checkEntry (single "function same(value: Word) returns (Word) { return value; } function same(value: Word) returns (Word) { return value + 1; } export {same};"))
  match discoverStaticWordRoots duplicate.program duplicate.moduleId with
  | .error (.duplicateSignature "same" "same" "same(uint256)") => pure ()
  | _ => throw (IO.userError "duplicate ABI signature diagnostic changed")
  let collision ← get "selector collision check" (checkEntry (single "function f116643(value: Word) returns (Word) { return value; } function f38491(value: Word) returns (Word) { return value; } export {f38491, f116643};"))
  match discoverStaticWordRoots collision.program collision.moduleId with
  | .error (.selectorCollision "f116643" "f38491" "f116643(uint256)" "f38491(uint256)" selector) =>
      require (selector.toUInt32.toNat == 0x77dbd42e) "selector conflict lost its canonical selector"
  | _ => throw (IO.userError "selector collision diagnostic changed")
  match checkEntry (single "function bad() returns (Word) { return absent; }") with
  | .error _ => pure () | .ok _ => throw (IO.userError "root discovery bypassed source checking")

end Tests.SourceCoreRootDiscovery
end

section
-- leanmerge: from Solcore.Test.SourceCoreShiftExecution
/-! Shift operators through the public source API (solcore-rs #129): `<<` and
`>>` on Words, their precedence between `+ -` and `&`, the compound `<<=` and
`>>=` on a local and on a mapping element, amounts at and past 256, and the two
adjacent tokens that spell them, so that nested type arguments still close with
two `>` tokens. Every expected value follows what the pinned Rust paths give
for Word shifts (lane D's probe and the `shift-operators` fixture, in
`docs/design/integer-types-unchecked-shifts.md`). -/
set_option autoImplicit false
namespace Tests.SourceCoreShiftExecution
open Solcore Solcore.Frontend SourceCoreExecution

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def word (n : Nat) : Value := .word (Core.Word.ofNatModulo n)
private def workspaceOf (lines : List String) : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [],
  mainSources := [{path := "main.solc", content := "pragma solcore;\n" ++ String.intercalate "\n" lines}] }

private def maximum : Nat := 2 ^ 256 - 1
private def high : Nat := 2 ^ 255

private def workspace : Workspace.RawWorkspace := workspaceOf [
  "function literalAmount(x: Word) returns (Word) { return x << 3; }",
  "function shiftLeft(x: Word, s: Word) returns (Word) { return x << s; }",
  "function shiftRight(x: Word, s: Word) returns (Word) { return x >> s; }",
  "function compound(x: Word, s: Word) returns (Word) { let r: Word = x; r <<= s; r >>= 1; return r; }",
  "function neverReverts(x: Word) returns (Word) { return x << 255; }",
  "function precedence(a: Word, b: Word) returns (Word) { return a + b << 2 & 0xff; }",
  "function comparisons(a: Word, b: Word) returns (Bool) { return a > b && a >= b; }",
  "function ladder(x: Word) returns (Word) { let w0: Word = x << 1 + 1; let w1: Word = x & 7 << 1; let w2: Word = x | 1 << 4; let w3: Word = 0; if (x >> 1 > 3) { w3 = 1; } let w4: Word = x << 2 * 3; let w5: Word = x ^ 1 << 2; return ((((w0 * 7 ^ w1) * 7 ^ w2) * 7 ^ w3) * 7 ^ w4) * 7 ^ w5; }",
  "function literals() returns (Word) { return 1 << 3 >> 1; }",
  "function shiftThenLess(a: Word, b: Word) returns (Bool) { return a << 1 < b; }",
  "function mapped(x: Word, s: Word) returns (Word) { let m: mapping(Bool => Word); m[true] = x; m[true] <<= s; m[true] >>= 1; return m[true]; }",
  "enum Box<T> { Box(T) }",
  "function nested(b: Box<Box<Word>>, x: Word) returns (Word) { return x >> 1; }"
]

private def names : List String :=
  ["literalAmount", "shiftLeft", "shiftRight", "compound", "neverReverts", "precedence",
    "comparisons", "ladder", "literals", "shiftThenLess", "mapped"]

private def seed (program : CheckedProgram) (name : String) : IO Seed :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure (SourceCoreCompiler.Seed.declaration signature.id)
  | _ => throw (IO.userError s!"shift fixture missing {name}")
private def execute {artifact : Artifact} (session : Session artifact) (key : Key) (arguments : List Value) :
    IO (Completion artifact) := do
  let executed ← session.runWithReceipt key arguments {executionFuel := 300000}
  match executed.val with
  | .ok (.succeeded result) => pure result
  | .ok (.exportError error _) => throw (IO.userError s!"shift export: {reprStr error}")
  | .ok (.failed reason _) => throw (IO.userError s!"shift language failure: {reprStr reason}")
  | .ok (.outOfFuel _) => throw (IO.userError "shift execution exhausted")
  | .error error => throw (IO.userError s!"shift invocation: {reprStr error}")
private def boot (artifact : Artifact) : IO (Session artifact) := do
  let fresh ← artifact.bootstrapWithReceipt
  match fresh.val.resume 300000 with
  | .ready session => pure session
  | .error error => throw (IO.userError s!"shift bootstrap: {reprStr error}")
  | .outOfFuel _ => throw (IO.userError "shift bootstrap exhausted")

/-- `x << 1 + 1`, `x & 7 << 1`, `x | 1 << 4`, `x >> 1 > 3`, `x << 2 * 3` and
`x ^ 1 << 2`, folded as the probe's `wordprec` method folds them. -/
private def ladderCases : List (Nat × Nat) :=
  [(0, 5492), (1, 72614), (3, 199304), (7, 472700), (8, 545277), (9, 592927),
    (255, 17116277), (high, 5541), (maximum, 52853)]

private def rejected (label : String) (lines : List String) : IO Unit :=
  match checkProgram (workspaceOf lines) with
  | .ok _ => throw (IO.userError s!"{label} was accepted")
  | .error _ => pure ()

def run : IO Unit := do
  let program ← get "shift check" (checkProgram workspace)
  let seeds ← names.mapM (seed program)
  let compiled ← get "shift compilation"
    (compile workspace seeds {specializationBudget := 256, compilationFuel := 1000})
  let key (index : Nat) : IO Key := match compiled.keys[index]? with
    | some key => pure key | none => throw (IO.userError "shift root missing")
  let mut session ← boot (← compiled.open)
  let wordCases : List (Nat × List Nat × Nat) :=
    [(0, [5], 40),
      (1, [1, 255], high), (1, [1, 256], 0), (1, [3, 1], 6), (1, [1, maximum], 0),
      (1, [maximum, 1], maximum - 1), (1, [0x100, 300], 0),
      (2, [high, 255], 1), (2, [maximum, 256], 0), (2, [0x100, 4], 0x10), (2, [0x100, 255], 0),
      (2, [maximum, maximum], 0), (2, [maximum, 3], maximum / 8),
      (3, [1, 8], 128), (3, [1, 300], 0),
      (4, [maximum], high),
      (5, [1, 2], 12), (5, [0x40, 0], 0),
      (8, [], 4),
      (10, [3, 4], 24), (10, [1, 256], 0), (10, [maximum, 1], high - 1)]
  for (index, arguments, expected) in wordCases do
    let completed ← execute session (← key index) (arguments.map word)
    require (completed.value == word expected)
      s!"shift case {names[index]?} {arguments} gave {reprStr completed.value}"
    session := completed.session
  for (input, expected) in ladderCases do
    let completed ← execute session (← key 7) [word input]
    require (completed.value == word expected) s!"shift precedence ladder {input} gave {reprStr completed.value}"
    session := completed.session
  let booleanCases : List (Nat × List Nat × Bool) :=
    [(6, [2, 1], true), (6, [1, 2], false), (9, [1, 3], true), (9, [2, 3], false)]
  for (index, arguments, expected) in booleanCases do
    let completed ← execute session (← key index) (arguments.map word)
    require (completed.value == .bool expected)
      s!"shift case {names[index]?} {arguments} gave {reprStr completed.value}"
    session := completed.session
  rejected "a shift spelled with separated tokens"
    ["function bad(a: Word, b: Word) returns (Word) { return a < < b; }"]
  rejected "a compound shift spelled with separated tokens"
    ["function bad(a: Word, b: Word) returns (Word) { a > >= b; return a; }"]
  rejected "a shift of a Bool"
    ["function bad(b: Bool) returns (Bool) { return b << 1; }"]
  rejected "a shift by a Bool"
    ["function bad(a: Word, b: Bool) returns (Word) { return a >> b; }"]
  IO.println "SOURCE_CORE_SHIFTS_PASS: Word `<<` and `>>` by amounts up to 2^256 - 1, their precedence between `+ -` and `&`, compound `<<=` and `>>=` on locals and mapping elements, nested type arguments closing with `>>`, and separated tokens rejected"

end Tests.SourceCoreShiftExecution
end

section
-- leanmerge: from Solcore.Test.SourceCoreSourceCells
/-! Real shared traversal uses source allocation hooks for lets and lambda
parameters. Parameter markers skip the packed argument and temporary payload
while preserving the order of earlier parameter and outer lexical references.
A lambda captures by value: it copies the outer cell when it is created and
again at each call, so the parameters' outer lexical reference is the call's
copy. -/

set_option autoImplicit false
namespace Tests.SourceCoreSourceCells
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open SourceCoreSourceCells

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"source_cells", by decide⟩], by decide⟩⟩, 0⟩
private def binder (index : Nat) (name : String) : TypedBinder :=
  ⟨⟨owner, index⟩, name, .mono .bool, [], false, none⟩
private def outer := binder 0 "outer"
private def first := binder 1 "first"
private def second := binder 2 "second"
private def localBinder := binder 3 "local"
private def expression (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def statement (index : Nat) : StatementId := ⟨⟨owner, index⟩⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "source_cells.solc"⟩, 0, 1⟩
private def allocate : Allocator := marked fun request =>
  pure ⟨⟨request.scope.length⟩, captureType request.scope⟩
private def reference : Ty := OptionalCell.referenceType .bool
private def definitions : DataEnvironment :=
  [⟨[.unit]⟩, ⟨[reference]⟩, ⟨[.product reference reference]⟩]
private def context : SourceCoreFunctions.Context := {
  plan := ⟨[], [], [], []⟩, owner := ⟨owner, []⟩, globals := [], administrativePrefix := 0,
  solvedRequirements := [], internalReason := Word.zero }
private def policy : SourceCoreFunctions.Policy := {sourceCells := some allocate}
private def lowerBody : SourceCoreFunctions.BodyLowerer :=
  fun child fuel source scope statements result reasonAt fellThrough escaped =>
    SourceCoreLoops.lowerStatementsWithPolicy {lowerExpression := child, sourceCells := some allocate}
      fuel source scope statements result reasonAt fellThrough escaped
private def lambdaSource : TypedSource := {
  owner, inputs := [outer], roots := [.expression (expression 0)], nodes := [
    .expression {id := expression 0, span, type := .function (.product .bool .bool) .bool, form := .lambda [first, second] .bool [statement 2]},
    .expression {id := expression 1, span, type := .bool, form := .reference "first" (.local first.id)},
    .statement {id := statement 2, span, type := .bool, form := .returnStmt (some (expression 1))}] }
private def letSource : TypedSource := {
  owner, inputs := [], roots := [.statement (statement 2), .statement (statement 3)], nodes := [
    .expression {id := expression 0, span, type := .bool, form := .reference "false" (.builtinBoolean false)},
    .expression {id := expression 1, span, type := .bool, form := .reference "local" (.local localBinder.id)},
    .statement {id := statement 2, span, type := .unit, form := .letDecl localBinder (some (expression 0))},
    .statement {id := statement 3, span, type := .bool, form := .returnStmt (some (expression 1))}] }
private def assertTrue (value : Bool) (message : String) : IO Unit := do
  unless value do throw (IO.userError message)

example : HasType [reference, .word, reference]
    (captures (Renaming.insertion 1) [(first.id, .bool), (outer.id, .bool)])
    (.product reference reference) definitions := by
  exact .pair (.var rfl) (.var rfl)

def run : IO Unit := do
  let .ok lowered := SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody 40 context lambdaSource
      [(outer.id, .bool)] (expression 0) (fun _ => Word.zero)
    | throw (IO.userError "shared lambda compiler rejected marked parameter allocation")
  let program : Core.Program := ⟨LanguageResult.resultType .bool,
    .letE (.newCell (OptionalCell.cellType .bool) (.inRight .unit (.bool true)))
      (TaggedFunction.call .bool lowered.expression (LanguageResult.success (.pair (.bool false) (.bool true)))),
    definitions⟩
  assertTrue program.check "marked lambda parameters failed whole Core checking"
  /- The store holds the outer cell, the creation copy of it (marker 1 and
  payload 2), the call's copy (marker 3, payload 4), then the parameters
  `first` (marker 5, payload 6) and `second` (marker 7, payload 8). -/
  match program.runStateful 10000 with
  | .done value store =>
      assertTrue (value == .inRight .word (.bool false) && store.length == 9)
        "marked parameter order or source result changed"
      assertTrue (SourceCoreHeapMarkers.completedPair ⟨⟨1⟩, reference⟩ store 1 ==
          some (.cellRef (OptionalCell.cellType .bool) 0, .inRight .unit (.bool true)) &&
        SourceCoreHeapMarkers.completedPair ⟨⟨1⟩, reference⟩ store 3 ==
          some (.cellRef (OptionalCell.cellType .bool) 2, .inRight .unit (.bool true)))
        "creation or call copy of the outer cell changed its marker or payload"
      assertTrue (SourceCoreHeapMarkers.completedPair ⟨⟨1⟩, reference⟩ store 5 ==
        some (.cellRef (OptionalCell.cellType .bool) 4, .inRight .unit (.bool false)))
        "first parameter captured the argument bundle or temporary payload"
      assertTrue (SourceCoreHeapMarkers.completedPair ⟨⟨2⟩, .product reference reference⟩ store 7 ==
        some (.pair (.cellRef (OptionalCell.cellType .bool) 6) (.cellRef (OptionalCell.cellType .bool) 4),
          .inRight .unit (.bool true)))
        "second parameter changed lexical capture order"
  | other => throw (IO.userError s!"marked parameter execution failed: {reprStr other}")
  let child : SourceCoreLoops.ExpressionLowerer := fun fuel source scope id reasonAt =>
    SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody fuel context source scope id reasonAt
  let .ok body := SourceCoreLoops.lowerStatementsWithPolicy {lowerExpression := child, sourceCells := some allocate}
      40 letSource [] [statement 2, statement 3] .bool (fun _ => Word.zero) Word.zero Word.zero
    | throw (IO.userError "shared statement compiler rejected marked let")
  let lets : Core.Program := ⟨LanguageResult.resultType .bool, body, definitions⟩
  assertTrue lets.check "marked let failed whole Core checking"
  match lets.runStateful 10000 with
  | .done value store =>
      assertTrue (value == .inRight .word (.bool false) && store.length == 2)
        "marked let changed its result or source allocation count"
  | other => throw (IO.userError s!"marked let execution failed: {reprStr other}")
  let .ok failedBody := letInitialized (some allocate) letSource [] Renaming.id localBinder .bool .bool
      (LanguageResult.failure .bool (.word (Word.ofNatModulo 71))) (LanguageResult.success (.bool true))
    | throw (IO.userError "marked initializer fault did not compile")
  let failed : Core.Program := ⟨LanguageResult.resultType .bool, failedBody, definitions⟩
  assertTrue failed.check "marked initializer fault failed Core checking"
  match failed.runStateful 10000 with
  | .done value store =>
      assertTrue (value == .inLeft .bool (.word (Word.ofNatModulo 71)) && store.isEmpty)
        "failed initializer allocated a marker or payload"
  | other => throw (IO.userError s!"marked initializer fault changed: {reprStr other}")
  let .ok absentBody := letUninitialized (some allocate) letSource [] Renaming.id localBinder .bool
      (OptionalCell.read .bool (.var 0) (Word.ofNatModulo 72))
    | throw (IO.userError "marked uninitialized source cell did not compile")
  let absent : Core.Program := ⟨LanguageResult.resultType .bool, absentBody, definitions⟩
  assertTrue absent.check "marked uninitialized source cell failed Core checking"
  match absent.runStateful 10000 with
  | .done value store =>
      assertTrue (value == .inLeft .bool (.word (Word.ofNatModulo 72)) &&
        SourceCoreHeapMarkers.completedPair ⟨⟨0⟩, .unit⟩ store 0 == some (.unit, .inLeft .bool .unit))
        "uninitialized source cell was replaced by a dummy value"
  | other => throw (IO.userError s!"marked uninitialized source cell changed: {reprStr other}")
  let .ok header := SourceCoreLoops.lowerForItems {lowerExpression := child, sourceCells := some allocate}
      (.declaration owner) 40 letSource [] [.letDecl localBinder (some (expression 0))] .bool
      (fun _ => Word.zero) (fun scope => do
        let read ← child 10 letSource scope (expression 1) (fun _ => Word.zero)
        pure (LocalLoop.returnValue .bool read.expression))
    | throw (IO.userError "marked for declaration did not compile")
  let forHeader : Core.Program := ⟨LocalLoop.resultType .bool, header, definitions⟩
  assertTrue forHeader.check "marked for declaration failed Core checking"
  match forHeader.runStateful 10000 with
  | .done value store =>
      assertTrue (value == LocalLoop.returnedValue (.bool false) && store.length == 2)
        "marked for declaration changed its scope or source cells"
  | other => throw (IO.userError s!"marked for declaration execution failed: {reprStr other}")
  /- The first parameter's marker-only boundary follows the outer cell and its
  two copies; the range covers completion after the copies. -/
  let mut sawPartial := false
  for fuel in List.range 200 do
    match program.runStateful fuel with
    | .outOfFuel checkpoint =>
        if checkpoint.store.length == 6 then
          sawPartial := true
          assertTrue ((SourceCoreHeapMarkers.completedPair ⟨⟨1⟩, reference⟩ checkpoint.store 5).isNone)
            "unfinished parameter allocation exported a source payload"
        match Core.runStateful 10000 checkpoint with
        | .done value _ => assertTrue (value == .inRight .word (.bool false)) "marked parameter resume changed"
        | other => throw (IO.userError s!"marked parameter resume failed: {reprStr other}")
    | .done value _ => assertTrue (value == .inRight .word (.bool false)) "marked parameter result changed"
    | .fault error _ => throw (IO.userError s!"marked parameter machine fault: {reprStr error}")
  assertTrue sawPartial "marked parameter checkpoints missed the marker-only boundary"
  IO.println "shared source allocation hooks and lexical parameter captures GREEN"

end Tests.SourceCoreSourceCells
end

section
-- leanmerge: from Solcore.Test.SourceCoreStagedClosedEvaluationMeaning
/-! The static boundary and actual accepted closed staged expressions. The
validation mode checks both branches; only execution mode has source meaning. -/
set_option autoImplicit false
namespace Tests.SourceCoreStagedClosedEvaluationMeaning
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference Solcore.TypeSystem
open Solcore.Frontend.SourceCoreElaboration
open Solcore.Frontend.SourceCoreElaboration.Internal

section Boundary
variable {solved : List SolvedRequirement} {source : TypedSource}
  {expression : ExpressionId}

theorem actual_integer {result : StagedIntegerEvaluation}
    (accepted : evaluateStagedInteger solved source expression = .ok result) :
    Staged.IntegerChecked solved source [] true (source.nodes.length + 1) expression result :=
  Staged.evaluateStagedInteger_checked accepted

theorem actual_word {result : StagedWordEvaluation}
    (accepted : evaluateStagedWord solved source expression = .ok result) :
    Staged.WordChecked solved source [] true (source.nodes.length + 1) expression result :=
  Staged.evaluateStagedWord_checked accepted

theorem actual_bool {result : StagedBoolEvaluation}
    (accepted : evaluateStagedBool solved source expression = .ok result) :
    Staged.BoolChecked solved source [] true (source.nodes.length + 1) expression result :=
  Staged.evaluateStagedBool_checked accepted

/-- Disabled evaluation returns a validation tree; this theorem assigns no
source meaning to its placeholder result. -/
theorem disabled_integer {environment : Staged.Environment} {fuel : Nat}
    {result : StagedIntegerEvaluation}
    (accepted : Staged.integer solved source environment false fuel expression = .ok result) :
    Staged.IntegerChecked solved source environment false fuel expression result :=
  Staged.integer_checked accepted

/-- Full callee validation remains attached to the actual ordered arguments. -/
theorem actual_callee {node : ExpressionNode} {callee : ExpressionId}
    {arguments : List ExpressionId} {function : BuiltinFunctionId}
    (checked : Staged.BuiltinChecked source node callee arguments function) :
    validateBuiltinFunctionCall source node callee arguments function = .ok () ∧
      node.requirements = [] ∧ node.coercions = [] :=
  ⟨checked.accepted, checked.requirements, checked.coercions⟩

/-- Consumed requirements form an ordered list, including repeated occurrences. -/
theorem repeated_consumption (requirement : RequirementId) :
    [requirement] ++ [requirement] = [requirement, requirement] ∧
      ([requirement] ++ [requirement]).length = 2 := ⟨rfl, rfl⟩
end Boundary


section SourceMeaning
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceStagedClosedEvaluationMeaning
variable {program : Program} {context : Solcore.SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {solved : List SolvedRequirement} {source : TypedSource}
  {environment : Dynamic.Environment} {heap : Dynamic.Heap} {expression : ExpressionId}

/-- The public accepted result itself supplies the exact receipt; no source
execution premise, unique-node assumption, or full-ledger validity is supplied. -/
theorem integer_source {result : StagedIntegerEvaluation}
    (ledger : context.solvedRequirements = solved)
    (accepted : evaluateStagedInteger solved source expression = .ok result)
    (valid : UsedValid context solved result.consumedRequirements) :
    Staged.IntegerChecked solved source [] true (source.nodes.length + 1) expression result ∧
    Dynamic.ExpressionEvaluates program context evidence source environment heap expression (.integer result.value) heap :=
  SourceStagedClosedEvaluationMeaning.evaluateStagedInteger_sound ledger accepted valid

theorem word_source {result : StagedWordEvaluation}
    (ledger : context.solvedRequirements = solved)
    (accepted : evaluateStagedWord solved source expression = .ok result)
    (valid : UsedValid context solved result.consumedRequirements) :
    Staged.WordChecked solved source [] true (source.nodes.length + 1) expression result ∧
    Dynamic.ExpressionEvaluates program context evidence source environment heap expression (.word result.value) heap :=
  SourceStagedClosedEvaluationMeaning.evaluateStagedWord_sound ledger accepted valid

theorem bool_source {result : StagedBoolEvaluation}
    (ledger : context.solvedRequirements = solved)
    (accepted : evaluateStagedBool solved source expression = .ok result)
    (valid : UsedValid context solved result.consumedRequirements) :
    Staged.BoolChecked solved source [] true (source.nodes.length + 1) expression result ∧
    Dynamic.ExpressionEvaluates program context evidence source environment heap expression (.bool result.value) heap :=
  SourceStagedClosedEvaluationMeaning.evaluateStagedBool_sound ledger accepted valid

/-- Actual function-local Integer cells are related by compiler lookup and
ordinary initialized source cells, without changing the heap. -/
theorem local_environment {actual : Staged.Environment} {fuel : Nat}
    {result : StagedIntegerEvaluation}
    (ledger : context.solvedRequirements = solved)
    (related : EnvironmentRep actual environment heap)
    (accepted : Staged.integer solved source actual true fuel expression = .ok result)
    (valid : UsedValid context solved result.consumedRequirements) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap expression (.integer result.value) heap :=
  (integer_of_accepted ledger related accepted valid).2

/-- A receipt that consumes no numeric requirements imposes no validity
condition on any ledger row, including unused implementation rows. -/
theorem no_numeric_validity {result : StagedBoolEvaluation}
    (ledger : context.solvedRequirements = solved)
    (accepted : evaluateStagedBool solved source expression = .ok result)
    (empty : result.consumedRequirements = []) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap expression (.bool result.value) heap := by
  apply (SourceStagedClosedEvaluationMeaning.evaluateStagedBool_sound ledger accepted ?_).2
  intro row proof member used implementation
  rw [empty] at used
  cases used

/-- The actual environment relation is vacuous for the closed public wrappers;
no assumptions on unrelated source heap cells are added. -/
theorem closed_environment : EnvironmentRep [] environment heap := EnvironmentRep.empty _ _
end SourceMeaning

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc", mainSources := [{ path := "main.solc", content := "pragma solcore;\n" ++ content }], externalLibraries := [] }

private def sourceText : String := String.intercalate "\n" [
  "function arithmetic() returns (Word) { return wordFromInteger((integerLt(1, 2) ? integerMul(integerAdd(3, 4), integerSub(9, 2)) : wordToInteger(17))); }",
  "function words() returns (Word) { return false ? 7 : 9; }",
  "function booleans() returns (Bool) { return true ? integerEq((1), (1)) : integerLt(3, 2); }",
  "function duplicate() returns (Word) { return wordFromInteger(integerAdd(3, 4)); }",
  "function unused() returns (Word) { return 31; }"
]

private def functionNamed (program : CheckedProgram) (name : String) : IO CheckedFunction :=
  match program.functions.find? fun fn =>
      (program.environment.declaration? fn.declaration).any fun decl => decl.name == some name with
  | some fn => pure fn
  | none => throw (IO.userError s!"missing staged fixture {name}")

private def returned (fn : CheckedFunction) : IO ExpressionId :=
  match fn.typedBody.roots with
  | [.statement statement] => match fn.typedBody.lookupStatement? statement with
    | some { form := .returnStmt (some expression), .. } => pure expression
    | _ => throw (IO.userError "missing staged return")
  | _ => throw (IO.userError "unexpected staged roots")

private def change (source : TypedSource) (expression : ExpressionId)
    (update : ExpressionNode → ExpressionNode) : TypedSource := {
  source with nodes := source.nodes.map fun
    | .expression node => if node.id = expression then .expression (update node) else .expression node
    | .statement node => .statement node }

private def wordResult (solved : List SolvedRequirement) (source : TypedSource)
    (expression : ExpressionId) : IO StagedWordEvaluation :=
  match evaluateStagedWord solved source expression with
  | .ok result => pure result
  | .error error => throw (IO.userError s!"word staging failed: {reprStr error}")

/-- Actual checker output exercises all seven builtins, all three conditional
result types, groups, disabled validation, and ordered complete consumption. -/
def run : IO Unit := do
  let program ← match checkProgram (workspace sourceText) with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"staged fixture checking: {reprStr error}")
  let unused ← functionNamed program "unused"
  -- The surrounding unused rows are explicit ledger augmentation. Their fresh
  -- ID is independent of the checker-produced requirement sequence.
  let unusedRow ← match unused.solvedRequirements with
    | [row] => pure { row with id := ⟨100000⟩ }
    | _ => throw (IO.userError "expected one unused numeric row")
  for (name, expected) in [("arithmetic", 49), ("words", 9), ("duplicate", 7)] do
    let fn ← functionNamed program name
    let root ← returned fn
    let result ← wordResult fn.solvedRequirements fn.typedBody root
    assertTrue (result.value == Core.Word.ofNatModulo expected &&
        result.consumedRequirements == fn.solvedRequirements.map (·.id))
      s!"{name}: value or complete ordered consumption changed"
    let extended := unusedRow :: (fn.solvedRequirements ++ [unusedRow])
    let padded ← wordResult extended fn.typedBody root
    assertTrue (padded == result) s!"{name}: unused prefix/suffix changed staging"
    match Staged.word extended fn.typedBody [] false (fn.typedBody.nodes.length + 1) root with
    | .ok disabled =>
        assertTrue (disabled.value == Core.Word.ofNatModulo (if name == "words" then 9 else 0))
          s!"{name}: validation-only placeholder boundary changed"
        assertTrue (disabled.consumedRequirements == result.consumedRequirements)
          s!"{name}: disabled traversal lost branch consumption"
    | .error error => throw (IO.userError s!"{name}: disabled validation failed: {reprStr error}")
  let boolFn ← functionNamed program "booleans"
  let boolRoot ← returned boolFn
  match evaluateStagedBool boolFn.solvedRequirements boolFn.typedBody boolRoot with
  | .ok result =>
      assertTrue (result.value && result.consumedRequirements == boolFn.solvedRequirements.map (·.id))
        "Bool group/conditional/comparison or all-branch consumption changed"
  | .error error => throw (IO.userError s!"Bool staging failed: {reprStr error}")
  let arithmetic ← functionNamed program "arithmetic"
  let arithmeticRoot ← returned arithmetic
  let inactive ← match arithmetic.typedBody.nodes.find? fun
      | .expression { form := .call _ _ (.builtinFunction .wordToInteger), .. } => true
      | _ => false with
    | some (.expression { form := .call callee _ _, .. }) => pure callee
    | _ => throw (IO.userError "missing inactive conversion callee")
  let tampered := change arithmetic.typedBody inactive fun node =>
    { node with form := .reference "wrongBuiltinSpelling" (.builtinFunction .wordToInteger) }
  assertTrue (match evaluateStagedWord arithmetic.solvedRequirements tampered arithmeticRoot with
    | .error _ => true | .ok _ => false)
    "malformed inactive callee escaped validation"
  assertTrue (match Staged.word arithmetic.solvedRequirements tampered [] false
    (tampered.nodes.length + 1) arithmeticRoot with | .error _ => true | .ok _ => false)
    "disabled validation ignored malformed callee"
  let duplicate ← functionNamed program "duplicate"
  let duplicateRoot ← returned duplicate
  let (call, callee, left) ← match duplicate.typedBody.nodes.find? fun
      | .expression { form := .call _ _ (.builtinFunction .integerAdd), .. } => true
      | _ => false with
    | some (.expression { id, form := .call callee [left, _] _, .. }) => pure (id, callee, left)
    | _ => throw (IO.userError "missing repeated-operand fixture")
  -- This retained IR mutation is checked by the actual evaluator; it is not
  -- asserted to be fresh parser/checker output.
  let repeated := change duplicate.typedBody call fun node =>
    { node with form := .call callee [left, left] (.builtinFunction .integerAdd) }
  let repeatedResult ← wordResult duplicate.solvedRequirements repeated duplicateRoot
  let requirement ← match repeated.lookupExpression? left with
    | some { form := .integerLiteral _ resolution, .. } => pure resolution.requirement
    | _ => throw (IO.userError "repeated operand is not a numeric literal")
  assertTrue (repeatedResult.value == Core.Word.ofNatModulo 6 &&
    repeatedResult.consumedRequirements == [requirement, requirement])
    "repeated operand consumption was deduplicated or reordered"

end Tests.SourceCoreStagedClosedEvaluationMeaning
end

section
-- leanmerge: from Solcore.Test.SourceCoreStagedExecution
/-! Actual compiled callable contracts preserve the source invocation observations.
The public session, internal source observation adapter and ordinary prepared
body all execute Core. Owned handles retain the actual native descriptor. -/

set_option autoImplicit false
namespace Tests.SourceCoreStagedExecution
open Solcore Solcore.Frontend
private def w (value : Nat) : Core.Word := Core.Word.ofNatModulo value

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [],
  mainSources := [{path := "main.solc", content := "pragma solcore;\n" ++ String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}", "impl Mark<Bool> {}",
    "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
    "function markedEffects(comptime seed: Word) returns (comptime<Word>) { let total: Word = seed; let table: mapping(Word => Word); let bump = lam(comptime delta: Word) -> Word { total += delta; table[0] = total; return table[0]; }; return bump(3); }",
    "function markedEffectsEntry() returns (Word) { return markedEffects(9); }",
    "function markedClosureClosed() returns (Word) { let f = lam(comptime value: Word) -> Word { return value; }; return f(21); }",
    "function markedClosureRuntime(value: Word) returns (Word) { let f = lam(comptime item: Word) -> Word { return item; }; return f(value); }",
    "function markedGlobal(comptime value: Word) returns (Word) { return value; }",
    "function markedGlobalClosed() returns (Word) { let f = markedGlobal; return f(22); }",
    "function markedGlobalRuntime(value: Word) returns (Word) { let f = markedGlobal; return f(value); }",
    "function markedResult(comptime value: Word) returns (comptime<Word>) { return value; }",
    "function markedResultIndirectBlocked() returns (Word) { let f = markedResult; return f(23); }",
    "function markedResultIndirectStaged() returns (comptime<Word>) { let f = markedResult; return f(24); }",
    "function tupleBefore() returns (Word) { let trace: Word = 0; let f = lam(value: (Word, Word)) -> Word { return 7; }; let bump = lam() -> Word { trace += 1; return trace; }; return f(bump(), bump()); }",
    "function tupleAfter() returns (comptime<Word>) { let trace: Word = 0; let f = lam(value: (Word, Word)) -> Word { return 7; }; let bump = lam() -> Word { trace += 1; return trace; }; return f(bump(), bump()); }",
    "function tupleAccepted() returns (Word) { let f = lam(value: (Word, Word)) -> Word { return 7; }; return f((1, 2)); }",
    "function polymorphic(flag: Bool) returns (Word, Bool) { let f = lam(item) { return keep(item); }; return (f(1), f(flag)); }",
    "function nested(flag: Bool) returns (Word, Word) { let outer = lam(item) { keep(item); let inner = lam(value) { return keep(value); }; return inner(1); }; let thirteen: Word = 13; return (outer(thirteen), outer(flag)); }",
    "type F = function(Word) returns (Word);",
    "function maker(seed: Word) returns (F) { let total: Word = seed; let f = lam(item) { keep(item); total += 1; return total; }; return f; }",
    "function use(f: F, item: Word) returns (Word) { return f(item); }",
    "function identities() returns (Word, Word) { let table: mapping(F => Word); table[markedGlobal] = 7; table[markedGlobal] = 9; let f = lam(item: Word) -> Word { return item; }; table[f] = 11; table[f] = 13; return (table[markedGlobal], table[f]); }",
    "function builtinCall(value: integer) returns (Word) { let f = wordFromInteger; return f(value); }"
  ]}]
}

private def key (program : CheckedProgram) (name : String) : IO SourceCoreGeneralFunctions.Key :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError s!"staged execution function missing: {name}")

private def plan (program : CheckedProgram) (keys : List SourceCoreGeneralFunctions.Key) : IO SourceCoreGeneralFunctions.Plan :=
  match SourceSpecializationWorklist.run program (keys.map fun key => ⟨key.declaration, []⟩) 128 with
  | .ok (.complete plan) => pure plan
  | result => throw (IO.userError s!"staged execution worklist failed: {reprStr result}")

private def prepare (program : CheckedProgram) (keys : List SourceCoreGeneralFunctions.Key) : IO SourceCoreSession.Recipe := do
  let plan ← plan program keys
  match SourceCoreSession.Recipe.prepareAutomatic program plan 256 true with
  | .ok recipe => pure recipe
  | .error error => throw (IO.userError s!"staged execution compile failed: {reprStr error}")

private def publicArgument : Core.Value → Option SourceCoreExecution.Value
  | .bool value => some (.bool value)
  | .word value => some (.word value)
  | .integer value => some (.integer value)
  | _ => none

private def legacyNative : SourceTypedRuntime.Value → Option Core.Value
  | .unit => some .unit
  | .bool value => some (.bool value)
  | .word value => some (.word value)
  | .integer value => some (.integer value)
  | .product left right => do pure (.pair (← legacyNative left) (← legacyNative right))
  | _ => none


/-- `trace`, when given, lists the Word cells of a faulting run's store. In the
tuple fixtures these are the `trace` local, the snapshots of it that `f` and
`bump` take when they are created, and one copy for each `bump` call that ran
before the fault. -/
private def check (program : CheckedProgram) (name : String) (arguments : List Core.Value)
    (expected : Option Core.Value) (trace : Option (List Core.Word) := none) : IO Unit := do
  let key ← key program name
  let recipe ← prepare program [key]
  let entry ← match recipe.program.findEntry? key with
    | some entry => pure entry
    | none => throw (IO.userError "staged cached entry missing")
  let compiled ← SourceCompilerFeatureSupport.compileNamed program name []
    {specializationBudget := 128, compilationFuel := 1000}
  let publicInputs ← match arguments.mapM publicArgument with
    | some values => pure values
    | none => throw (IO.userError "staged fixture has unsupported public input")
  let old := (← compiled.audit publicInputs).observation
  let verify := fun observation diagnosticAt => do
    match observation, old, expected with
    | .succeeded value _, .done oldValue _, some expected =>
        unless value == expected && legacyNative oldValue == some expected do
          throw (IO.userError s!"{name} staged result changed: {reprStr value}")
    | .failed reason store, .fault oldError _, none =>
        let diagnostic ← match diagnosticAt reason with
          | some diagnostic => pure diagnostic
          | none => throw (IO.userError s!"{name} lost staged diagnostic")
        unless diagnostic.error == oldError do
          throw (IO.userError s!"{name} staged diagnostic differs: {reprStr diagnostic.error}; old: {reprStr oldError}")
        if let some trace := trace then
          let scalars := store.filterMap fun | .inRight .unit (.word value) => some value | _ => none
          unless scalars == trace do throw (IO.userError s!"{name} changed argument/parameter effects: {reprStr scalars}")
    | observation, _, _ => throw (IO.userError s!"{name} staged outcome changed: {reprStr observation}")
  for _ in [0, 1] do
    match entry.run arguments 65536 with
    | .ok result => verify result.observation entry.faultSites.diagnostic?
    | .error error => throw (IO.userError s!"{name} staged input rejected: {reprStr error}")
  match entry.run arguments 0 with
  | .ok {observation := .outOfFuel state, ..} => verify (Core.LanguageResult.observeResult (Core.runStateful 65536 state)) entry.faultSites.diagnostic?
  | _ => throw (IO.userError s!"{name} staged entry did not suspend")
  for _ in [0, 1] do
    let invoked ← compiled.invoke publicInputs
    match invoked.outcome, old with
    | .succeeded completion, .done value _ =>
        let observed ← SourceCompilerFeatureSupport.get "public staged value"
          (SourceCompilerFeatureSupport.rawData 128 completion.value)
        unless reprStr observed == reprStr value do
          throw (IO.userError s!"{name} public staged value changed")
    | .failed reason _, .fault error _ =>
        match ← invoked.diagnostic reason with
        | some diagnostic => unless diagnostic.error == error do
            throw (IO.userError s!"{name} public staged diagnostic changed")
        | none => throw (IO.userError s!"{name} public staged diagnostic missing")
    | _, _ => throw (IO.userError s!"{name} public staged classification changed")
  let artifact ← compiled.execution.open
  let session ← SourceCompilerFeatureSupport.boot artifact
  let checkpoint ← SourceCompilerFeatureSupport.get "public staged checkpoint" (session.start compiled.key publicInputs)
  let pending ← match ← checkpoint.resume 0 with
    | .outOfFuel pending => pure pending
    | _ => throw (IO.userError "public staged zero fuel did not suspend")
  match ← pending.resume 300000 with
  | .succeeded completion =>
      match old with
      | .done value _ =>
          let observed ← SourceCompilerFeatureSupport.get "public staged resumed value"
            (SourceCompilerFeatureSupport.rawData 128 completion.value)
          unless reprStr observed == reprStr value do throw (IO.userError "public staged resume changed result")
      | _ => throw (IO.userError "public staged resume changed fault into success")
  | .failed reason session =>
      match old, ← SourceCompilerFeatureSupport.get "public resumed diagnostic" (session.diagnostic compiled.key reason) with
      | .fault error _, some diagnostic =>
          unless diagnostic.error == error do throw (IO.userError "public staged resume changed diagnosis")
      | _, _ => throw (IO.userError "public staged resume changed fault")
  | _ => throw (IO.userError "public staged resume did not complete")

def run : IO Unit := do
  let program ← match checkProgram workspace 4096 with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"staged source rejected: {reprStr error}")
  check program "markedEffects" [.word (w 9)] (some (.word (w 12)))
  check program "markedEffectsEntry" [] (some (.word (w 12)))
  check program "markedClosureClosed" [] (some (.word (w 21)))
  check program "markedClosureRuntime" [.word (w 25)] none
  check program "markedGlobalClosed" [] (some (.word (w 22)))
  check program "markedGlobalRuntime" [.word (w 25)] none
  check program "markedResultIndirectBlocked" [] none
  check program "markedResultIndirectStaged" [] (some (.word (w 24)))
  -- No argument runs before the fault, so no call copy of `trace` exists.
  check program "tupleBefore" [] none (some [w 0, w 0, w 0])
  -- Both `bump()` arguments run before the fault, each from the snapshot 0.
  check program "tupleAfter" [] none (some [w 0, w 0, w 0, w 1, w 1])
  check program "tupleAccepted" [] (some (.word (w 7)))
  check program "identities" [] (some (.pair (.word (w 9)) (.word (w 0))))
  check program "builtinCall" [.integer 42] (some (.word (w 42)))
  for flag in [true, false] do
    check program "polymorphic" [.bool flag] (some (.pair (.word (w 1)) (.bool flag)))
    check program "nested" [.bool flag] (some (.pair (.word (w 1)) (.word (w 1))))
  let producer ← key program "maker"
  let consumer ← key program "use"
  let recipe ← prepare program [producer, consumer]
  let artifact ← recipe.open
  let session ← artifact.newSession
  match ← session.run producer [.word (w 10)] 65536 256 with
  | .ok (.succeeded made) =>
      let handle ← match made.value with
        | .function handle => pure handle
        | _ => throw (IO.userError "staged closure was not exported as owned handle")
      unless made.session.functionIdentity? handle == some .anonymous do
        throw (IO.userError "wrapper lost anonymous owned identity")
      match ← made.session.run consumer [made.value, .word (w 1)] 65536 256 with
      | .ok (.succeeded first) =>
          unless first.value == .word (w 11) do throw (IO.userError "staged handle lost its capture")
          match ← first.session.run consumer [made.value, .word (w 2)] 65536 256 with
          | .ok (.succeeded second) =>
              unless second.value == .word (w 11) do throw (IO.userError "staged handle call did not restart from its captured seed")
          | _ => throw (IO.userError "staged handle second invocation failed")
      | _ => throw (IO.userError "staged handle invocation failed")
  | _ => throw (IO.userError "staged handle export failed")
  IO.println "actual staged Core compilation, guards, effects and owned captures GREEN"

end Tests.SourceCoreStagedExecution
end

section
-- leanmerge: from Solcore.Test.SourceCoreStagedIntegerLetMeaning
/-! Actual Integer-let lowering: the resolved body omits this let, while the
independent source step allocates its exact Integer cell. -/
set_option autoImplicit false
namespace Tests.SourceCoreStagedIntegerLetMeaning
open Solcore Frontend SourceInference TypeSystem SourceCoreElaboration
open SourceCoreElaboration.Internal SourceSemantics SourceSemantics.CoreLowering
open SourceStagedClosedEvaluationMeaning SourceStagedIntegerStatementsMeaning

abbrev actual_erased_step := @SourceStagedIntegerLetMeaning.let_erased_step

abbrev actual_let := @SourceStagedIntegerLetMeaning.let_of_accepted
abbrev actual_function_head := @SourceStagedIntegerLetMeaning.function_head_source_step
abbrev actual_typed_extension := @SourceStagedIntegerLetMeaning.typed_extension

theorem actual_draft {function : CheckedFunction} {draft : BodyDraft}
    (accepted : lowerFunctionBody function = .ok draft) :
    Staged.IntegerLet.FunctionAccepted function draft := Staged.IntegerLet.function_of_accepted accepted

theorem actual_remainder {function : CheckedFunction} {draft : BodyDraft}
    (accepted : lowerFunctionBody function = .ok draft) :
    ∃ consumed, reconcileConsumedRequirements function.declaration
      (function.solvedRequirements.map (·.id)) consumed = .ok draft.unconsumedRequirements := by
  cases Staged.IntegerLet.function_of_accepted accepted with
  | intro owned rootsAccepted rootsSame nonempty inputsAccepted expectedAccepted bodyAccepted reconciled declaration inputEq resolved returnType rootOccurrence =>
    exact ⟨_, reconciled⟩

theorem prior_cell {before after : Dynamic.Heap} {value : Int}
    {location : Dynamic.Location} {cell : Dynamic.Cell}
    (extended : Extends before after [value]) (original : Dynamic.Heap.Reads before location cell) :
    Dynamic.Heap.Reads after location cell := extended.preserves_read original

/-- An erased source let still allocates; the source heaps cannot be equated. -/
theorem source_grows {before after : Dynamic.Heap} {value : Int}
    (extended : Extends before after [value]) : after ≠ before := by
  have length := extended.length_eq
  simp only [List.length_cons, List.length_nil] at length
  intro same
  subst after
  omega

/-- Empty quantified variables alone do not establish source binder extension. -/
theorem malformed_scheme {source : TypedSource} {context next : SourceSemantics.Context} {binder : TypedBinder}
    (mono : binder.scheme.quantified = []) (nonempty : binder.schemeRequirements ≠ [])
    (extended : BinderExtends source.owner context binder next) : False := by
  cases extended with
  | intro wellFormed fresh => exact nonempty (wellFormed.monomorphic_requirements_empty mono)

/-- A valid draft can retain unused ledger rows; finalization rejects them. -/
theorem nonempty_remainder {draft : BodyDraft} {head : RequirementId} {tail : List RequirementId}
    (remaining : draft.unconsumedRequirements = head :: tail) :
    draft.finalize = .error ⟨.declaration draft.declaration, .unconsumedRequirements (head :: tail)⟩ := by
  unfold BodyDraft.finalize
  rw [remaining]
  rfl

private def require (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def get {α : Type} (message : String) : Except SourceCoreElaboration.Error α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{message}: {reprStr error}")

private def content : String := String.intercalate "\n" [
  "function basic() returns (Word) { let x: integer = 42; let y: integer = integerAdd(x, 8); return wordFromInteger(integerMul(y, 2)); }",
  "function negative() returns (Word) { let x: integer = integerSub(0, 3); return wordFromInteger(x); }",
  "function chosen() returns (Word) { let x: integer = true ? integerAdd(2, 3) : integerMul(6, 7); return wordFromInteger(x); }",
  "function reuse() returns (Word) { let x: integer = 3; return wordFromInteger(integerAdd(x, x)); }",
  "function unused() returns (Word) { let ignored: integer = integerAdd(20, 22); return 7; }",
  "function shadow() returns (Word) { let x: integer = 3; let x: integer = integerAdd(x, 1); return wordFromInteger(x); }",
  "function runtime(value: Word) returns (Word) { let x: integer = 2; return value; }",
  "function helper() returns (integer) { return 3; }",
  "function direct() returns (Word) { let x: integer = helper(); return wordFromInteger(x); }"
]

private def named (program : CheckedProgram) (name : String) : IO CheckedFunction :=
  match program.functions.find? fun function =>
      (program.environment.declaration? function.declaration).any fun entry => entry.name == some name with
  | some function => pure function
  | none => throw (IO.userError s!"missing function {name}")

private def roots (function : CheckedFunction) : IO (List StatementId) :=
  function.typedBody.roots.mapM fun
    | .statement statement => pure statement
    | .expression _ => throw (IO.userError "unexpected expression root")

private def whole (function : CheckedFunction) : IO LoweredExpression := do
  let scope ← get "actual inputs" (Staged.IntegerLet.inputScope function.typedBody.inputs)
  let expected ← get "actual result projection" (lowerType (.declaration function.declaration) function.inferredBodyType)
  let statements ← roots function
  let site := match Staged.IntegerLet.lastStatement statements with
    | some last => ErrorSite.occurrence last.occurrence | none => .declaration function.declaration
  get "actual statement lowerer" (Staged.IntegerLet.lower function.solvedRequirements function.typedBody scope []
    (function.typedBody.nodes.length + 1) expected site .statementListFallthrough statements)

private def inspect (function : CheckedFunction) (expectedInitial : Int) : IO Unit := do
  let statements ← roots function
  let (statement, rest) ← match statements with
    | first :: rest => pure (first, rest) | [] => throw (IO.userError "empty roots")
  let (node, binder, initializer) ← match function.typedBody.lookupStatement? statement with
    | some node => match node.form with
      | .letDecl binder (some initializer) => pure (node, binder, initializer)
      | _ => throw (IO.userError "expected Integer let")
    | none => throw (IO.userError "missing head")
  require (node.type == Ty.unit && binder.scheme.quantified.isEmpty && binder.scheme.body == Ty.integer)
    "actual first let metadata"
  let scope ← get "actual scope" (Staged.IntegerLet.inputScope function.typedBody.inputs)
  let expected ← get "actual return type" (lowerType (.declaration function.declaration) function.inferredBodyType)
  let site := match Staged.IntegerLet.lastStatement statements with
    | some last => ErrorSite.occurrence last.occurrence | none => .declaration function.declaration
  let fuel := function.typedBody.nodes.length
  let initial ← get "actual initializer" (Staged.integer function.solvedRequirements function.typedBody [] true fuel initializer)
  require (initial.value == expectedInitial) "initializer source order/value"
  let environment := [Staged.Statements.bind binder initial.value]
  let body ← get "actual body under Integer head" (Staged.IntegerLet.lower function.solvedRequirements function.typedBody
    scope environment fuel expected site .statementListFallthrough rest)
  let result ← whole function
  let draft ← get "actual public draft" (lowerFunctionBody function)
  require (result.resolved == body.resolved && result.consumedRequirements == initial.consumedRequirements ++ body.consumedRequirements)
    "Integer head erasure or ordered consumption changed"
  require (draft.inputs == scope && draft.resolved == result.resolved && draft.returnType == expected &&
    draft.unconsumedRequirements.isEmpty && result.consumedRequirements == function.solvedRequirements.map (·.id))
    "public receipt lost same actual scope/body/full reconciliation"
  let _ ← get "actual finalization" draft.finalize
  -- The original compiler environment duplicate guards precede all children.
  for (badScope, badEnvironment) in [((binder.id, Core.Ty.word) :: scope, ([] : Staged.Environment)), (scope, environment)] do
    match Staged.IntegerLet.lower function.solvedRequirements function.typedBody badScope badEnvironment
        (fuel + 1) expected site .statementListFallthrough statements with
    | .error {reason := .duplicateLocal actual, ..} => require (actual == binder.id) "duplicate guard identity"
    | _ => throw (IO.userError "duplicate let accepted")

private def reject (function : CheckedFunction) : IO Unit :=
  match lowerFunctionBody function with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "malformed or unsupported let accepted")

/-- Real checker fixtures and explicitly modified retained IR are separate.
IO inspects compiler erasure, not a source/runtime heap equivalence. -/
def run : IO Unit := do
  let program ← match checkProgram {entry := "main.solc", mainSources := [{path := "main.solc", content := "pragma solcore;\n" ++ content}], externalLibraries := []} with
    | .ok program => pure program | .error errors => throw (IO.userError s!"Integer let checker: {reprStr errors}")
  for (name, value) in [("basic", 42), ("negative", -3), ("chosen", 5), ("reuse", 3), ("unused", 42), ("shadow", 3), ("runtime", 2)] do
    inspect (← named program name) value
  reject (← named program "direct")
  let basic ← named program "basic"
  let statements ← roots basic
  let first ← match statements.head? with | some first => pure first | none => throw (IO.userError "no head")
  let (node, binder, initializer) ← match basic.typedBody.lookupStatement? first with
    | some node => match node.form with
      | .letDecl binder (some initializer) => pure (node, binder, initializer)
      | _ => throw (IO.userError "missing let")
    | none => throw (IO.userError "missing statement")
  let foreign ← named program "negative"
  for changed in [{node with form := .letDecl {binder with id := {binder.id with owner := foreign.declaration}} (some initializer)},
      {node with type := .word}, {node with form := .letDecl binder none},
      {node with form := .letDecl {binder with scheme := {binder.scheme with quantified := [⟨999⟩]}} (some initializer)}] do
    reject {basic with typedBody := {basic.typedBody with nodes := basic.typedBody.nodes.map fun
      | .statement old => if old.id == first then .statement changed else .statement old
      | other => other}}
  -- Validation also checks the unselected initializer arm.
  let chosen ← named program "chosen"
  let no ← match chosen.typedBody.nodes.filterMap (fun
      | .expression {form := .conditional _ _ no, ..} => some no | _ => none) with
    | [no] => pure no | _ => throw (IO.userError "conditional fixture")
  reject {chosen with typedBody := {chosen.typedBody with nodes := chosen.typedBody.nodes.map fun
    | .expression old => if old.id == no then .expression {old with type := .word} else .expression old
    | other => other}}
  -- Draft acceptance keeps every unused row in order; only finalize rejects.
  let extra ← match basic.solvedRequirements.head? with
    | some row => pure {row with id := ⟨100000⟩} | none => throw (IO.userError "no numeric evidence")
  let augmented := {basic with solvedRequirements := extra :: basic.solvedRequirements ++ [extra]}
  let original ← whole basic
  let retained ← whole augmented
  require (original == retained) "unused prefix/suffix ledger altered private traversal"
  let draft ← get "augmented public draft must remain accepted" (lowerFunctionBody augmented)
  require (draft.resolved == retained.resolved && draft.unconsumedRequirements == [extra.id, extra.id])
    "draft lost full unused ledger order"
  match draft.finalize with
  | .error {reason := .unconsumedRequirements remaining, ..} => require (remaining == [extra.id, extra.id]) "finalize exact remainder"
  | _ => throw (IO.userError "finalize accepted unused evidence")
end Tests.SourceCoreStagedIntegerLetMeaning
end

section
-- leanmerge: from Solcore.Test.SourceCoreStagedIntegerResidualMeaning
/-! Actual pure compatibility elaboration with retained scalar inputs and
Integer-let erasure. The Source heap and Core store remain distinct states. -/
set_option autoImplicit false
namespace Tests.SourceCoreStagedIntegerResidualMeaning
open Solcore Frontend SourceInference TypeSystem SourceCoreElaboration
open SourceCoreElaboration.Internal SourceSemantics SourceSemantics.CoreLowering
open SourceStagedIntegerResidualMeaning

abbrev actual_expression := @expression_meaning
abbrev actual_statements := @statements_of_accepted
abbrev actual_public_function := @elaborateFunction_sound
abbrev retained_inputs := @inputs_heaps
abbrev actual_typed_inputs := @inputs_typed
abbrev actual_dropped_binding := @MixedEnvironment.erase_allocated

theorem artifact_type (artifact : ElaboratedFunction) :
    Resolved.HasType artifact.inputs artifact.resolved artifact.returnType := artifact_typed artifact

/-- Integer-let execution grows the Source heap even when Core stays pure. -/
theorem source_heap_grows {before after : Dynamic.Heap} {head : Int} {tail : List Int}
    (cells : SourceStagedIntegerStatementsMeaning.Extends before after (head :: tail)) : after ≠ before := by
  have length := cells.length_eq
  intro same
  subst after
  simp only [List.length_cons] at length
  omega

/-- The full captured-environment relation cannot drop a lexical row. -/
theorem captures_keep_length {mapping : SourceStagingHeapRelation.LocationMap}
    {source residual : Dynamic.Environment}
    (related : SourceStagingHeapRelation.EnvironmentRel mapping source residual) :
    source.length = residual.length := related.length

/-- The scalar ABI deliberately excludes staged Integer payloads. -/
theorem integer_is_not_runtime_scalar (value : Int) (native : Core.Value) :
    ¬ ScalarRep (.integer value) native := by intro impossible; cases impossible

/-- Runtime Word and Bool cells cannot occupy a dropped mapping position. -/
theorem runtime_scalar_not_dropped {mapping : SourceStagingHeapRelation.LocationMap}
    {source residual : Dynamic.Heap} {location : Dynamic.Location}
    {value : Dynamic.Value} {native : Core.Value} {type : TypeSystem.Ty}
    (related : SourceStagingHeapRelation.HeapRel mapping source residual)
    (read : Dynamic.Heap.Reads source location {type := type, value := some value})
    (scalar : ScalarRep value native)
    (dropped : mapping[location.index]? = some none) : False := by
  obtain ⟨cell, found, integer, equal⟩ := related.dropped location.index dropped
  cases read with
  | intro actual =>
    have selectedEq : ∀ {cells index cell}, Dynamic.Heap.CellAt cells index cell → cells[index]? = some cell := by
      intro cells index cell selected
      induction selected with
      | head => rfl
      | tail selected ih => exact ih
    have actualEq := selectedEq actual
    have same := Option.some.inj (actualEq.symm.trans found)
    have values := congrArg Dynamic.Cell.value (same.trans equal)
    cases scalar <;> cases values

theorem pure_store {environment : Resolved.Environment} {before after : Core.Store}
    {expression : Resolved.Expr} {value : Core.Value}
    (evaluated : Resolved.Evaluates environment before expression value after) : after = before :=
  evaluated.store_eq

private def require (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def get {α : Type} (message : String) : Except SourceCoreElaboration.Error α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{message}: {reprStr error}")
private def word (value : Nat) : Core.Value := .word (Core.Word.ofNatModulo value)

private def content : String := String.intercalate "\n" [
  "function scalar(flag: Bool, value: Word) returns (Word) { let x: integer = integerAdd(20, 22); return flag ? value : wordFromInteger(x); }",
  "function equal(value: Word) returns (Bool) { let x: integer = 3; let y: integer = integerMul(x, 2); return integerEq(y, 6); }",
  "function less(flag: Bool) returns (Bool) { let x: integer = integerSub(0, 3); return flag ? integerLt(x, 0) : false; }",
  "function branches(flag: Bool, value: Word) returns (Word) { if (flag) { let x: integer = 10; return wordFromInteger(x); } else { let y: integer = 99; return value; } }",
  "function block(value: Word) returns (Word) { { let x: integer = 5; let y: integer = integerAdd(x, x); return (wordFromInteger(y)); } }",
  "function empty(flag: Bool) returns (Bool) { return flag; }",
  "function literal() returns (Word) { return 7; }",
  "function arithmetic() returns (Word) { let x: integer = true ? integerMul(6, 7) : integerSub(0, 1); return wordFromInteger(x); }"
]

private def named (program : CheckedProgram) (name : String) : IO CheckedFunction :=
  match program.functions.find? fun function =>
      (program.environment.declaration? function.declaration).any fun entry => entry.name == some name with
  | some function => pure function
  | none => throw (IO.userError s!"missing residual function {name}")

private def inspect (function : CheckedFunction) (native : List Core.Value) (expectedValue : Core.Value) : IO Unit := do
  let scope ← get "actual input scope" (Staged.IntegerLet.inputScope function.typedBody.inputs)
  let projected ← get "actual return type" (lowerType (.declaration function.declaration) function.inferredBodyType)
  let roots := SourceStagedIntegerResidualMeaning.statementRoots function.typedBody
  let fuel := function.typedBody.nodes.length + 1
  require (Staged.Residual.statementsSupported function.typedBody fuel roots) "actual supported statement tree"
  let site := match Staged.IntegerLet.lastStatement roots with
    | some last => ErrorSite.occurrence last.occurrence | none => .declaration function.declaration
  let result ← get "actual lowering" (Staged.IntegerLet.lower function.solvedRequirements function.typedBody
    scope [] fuel projected site .statementListFallthrough roots)
  let draft ← get "actual draft" (lowerFunctionBody function)
  let artifact ← get "actual public elaboration" (elaborateFunction function)
  require (scope == draft.inputs && scope == artifact.inputs && result.resolved == draft.resolved &&
    result.resolved == artifact.resolved && projected == artifact.returnType && draft.unconsumedRequirements.isEmpty)
    "draft/finalized artifact differs from the accepted private result"
  require (result.consumedRequirements == function.solvedRequirements.map (·.id)) "ordered whole consumed ledger"
  require (artifact.resolved.lower? artifact.inputs.ids == some artifact.core &&
    Core.infer? artifact.inputs.values artifact.core == some artifact.returnType) "actual positional/type receipts"
  let store : Core.Store := [.bool true, .unit, .integer (-17), word 901]
  for fuel in [0, 1, 2, 5] do
    let actual := match Core.runStateful fuel (.initial artifact.core native store) with
      | .outOfFuel remaining => Core.runStateful 200 remaining
      | result => result
    require (actual == .done expectedValue store) "pure actual code result/full original store or resume changed"

/-- The IO fixtures exercise the actual default compatibility API. They do not
stand in for a public unified compilation or physical-cell correspondence. -/
def run : IO Unit := do
  let program ← match checkProgram {entry := "main.solc", mainSources := [{path := "main.solc", content := "pragma solcore;\n" ++ content}], externalLibraries := []} with
    | .ok program => pure program | .error errors => throw (IO.userError s!"residual checker: {reprStr errors}")
  for (name, values, expected) in [
      ("scalar", [.bool true, word 77], word 77), ("scalar", [.bool false, word 77], word 42),
      ("equal", [word 0], .bool true), ("less", [.bool true], .bool true), ("less", [.bool false], .bool false),
      ("branches", [.bool true, word 31], word 10), ("branches", [.bool false, word 31], word 31),
      ("block", [word 12], word 10), ("empty", [.bool false], .bool false),
      ("literal", [], word 7), ("arithmetic", [], word 42)] do
    inspect (← named program name) values expected
  let scalar ← named program "scalar"
  let extra ← match scalar.solvedRequirements.head? with
    | some row => pure {row with id := ⟨100000⟩} | none => throw (IO.userError "missing numeric row")
  let original ← get "original draft" (lowerFunctionBody scalar)
  let augmented ← get "unused ordered rows draft" (lowerFunctionBody {scalar with solvedRequirements := extra :: scalar.solvedRequirements ++ [extra]})
  require (augmented.resolved == original.resolved && augmented.unconsumedRequirements == [extra.id, extra.id])
    "unused prefix/suffix ledger was filtered or reordered"
  match augmented.finalize with
  | .error {reason := .unconsumedRequirements remaining, ..} =>
      require (remaining == [extra.id, extra.id]) "exact unused remainder"
  | _ => throw (IO.userError "unused ledger passed actual finalization")
  -- This retained-IR modification targets the dynamically unselected arm.
  let scalar ← named program "scalar"
  let no ← match scalar.typedBody.nodes.filterMap (fun
      | .expression {form := .conditional _ _ no, ..} => some no | _ => none) with
    | [no] => pure no | _ => throw (IO.userError "missing conditional")
  let tampered := {scalar with typedBody := {scalar.typedBody with nodes := scalar.typedBody.nodes.map fun
    | .expression node => if node.id == no then .expression {node with requirements := [⟨100001⟩]} else .expression node
    | node => node}}
  match elaborateFunction tampered with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "tampered unselected arm escaped validation")
end Tests.SourceCoreStagedIntegerResidualMeaning
end

section
-- leanmerge: from Solcore.Test.SourceCoreStagedIntegerStatementsMeaning
/-! Actual closed Integer statement/function acceptance. Both branches remain
in validation and consumed order; source allocations are covered by the formal
consumers and are not identified with the erased runtime heap. -/
set_option autoImplicit false
namespace Tests.SourceCoreStagedIntegerStatementsMeaning
open Solcore Frontend SourceInference TypeSystem SourceCoreElaboration
open SourceCoreElaboration.Internal

section Static

theorem actual_function {function : CheckedFunction} {arguments : List Int} {value : Int}
    (accepted : evaluateStagedIntegerFunction function arguments = .ok value) :
    Staged.Statements.FunctionChecked function arguments value := Staged.Statements.function_checked accepted

theorem actual_statements {source : TypedSource} {solved : List SolvedRequirement}
    {environment : Staged.Environment} {execute : Bool} {fuel : Nat}
    {site : ErrorSite} {reason : ErrorReason} {roots : List StatementId} {result : StagedIntegerEvaluation}
    (accepted : Staged.Statements.evaluate solved source environment execute fuel site reason roots = .ok result) :
    Staged.Statements.Checked solved source environment execute fuel roots result := Staged.Statements.checked accepted

theorem actual_inputs {source : TypedSource} {seen : List Resolved.LocalId}
    {binders : List TypedBinder} {values : List Int} {environment : Staged.Environment}
    (accepted : Staged.Statements.bindInputs source seen binders values = .ok environment) :
    Staged.Statements.InputsChecked source seen binders values environment := Staged.Statements.inputs_checked accepted

/-- Acceptance supplies the full original roots and complete reconciliation. -/
theorem full_roots_and_ledger {function : CheckedFunction} {arguments : List Int} {value : Int}
    (accepted : evaluateStagedIntegerFunction function arguments = .ok value) :
    ∃ environment roots result,
      roots.map NodeId.statement = function.typedBody.roots ∧
      Staged.Statements.Checked function.solvedRequirements function.typedBody environment true
        (function.typedBody.nodes.length + 1) roots result ∧ result.value = value ∧
      reconcileConsumedRequirements function.declaration
        (function.solvedRequirements.map (·.id)) result.consumedRequirements = .ok [] := by
  cases Staged.Statements.function_checked accepted with
  | intro owned arity inferred type inputs roots checked value reconciled =>
    exact ⟨_, _, _, roots, checked, value, reconciled⟩

/-- The native staged binder validator does not replace source binder typing. -/
theorem malformed_scheme_has_no_source_extension
    {source : TypedSource} {context final : SourceSemantics.Context} {binder : TypedBinder}
    (mono : binder.scheme.quantified = []) (nonempty : binder.schemeRequirements ≠ [])
    (extended : SourceSemantics.BinderExtends source.owner context binder final) : False := by
  cases extended with
  | intro wellFormed fresh => exact nonempty (wellFormed.monomorphic_requirements_empty mono)
end Static

section SourceMeaning
open SourceSemantics SourceSemantics.CoreLowering
open SourceStagedClosedEvaluationMeaning SourceStagedIntegerStatementsMeaning

/-- Public acceptance closes both the original ordered input allocation and
source statements. Original cells and selected let allocations remain explicit. -/
theorem actual_function_source
    {function : CheckedFunction} {arguments : List Int} {value : Int}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {before : Dynamic.Heap} {facts : BodyFacts}
    (accepted : evaluateStagedIntegerFunction function arguments = .ok value)
    (unique : NodeOccurrencesUnique function.typedBody)
    (typed : BodyHasType function.typedBody context .integer facts)
    (ledger : context.solvedRequirements = function.solvedRequirements)
    (valid : UsedValid context function.solvedRequirements (function.solvedRequirements.map (·.id))) :
    Staged.Statements.FunctionChecked function arguments value ∧
      ∃ environment bound roots final after added,
        roots.map NodeId.statement = function.typedBody.roots ∧
        Dynamic.BindersAllocate [] before function.typedBody.inputs
          (arguments.map Dynamic.Value.integer) environment bound ∧
        Dynamic.StatementsExecute program context evidence function.typedBody environment bound roots final
          (.returned (.integer value)) after ∧ Extends before after (arguments ++ added) :=
  SourceStagedIntegerStatementsMeaning.evaluateStagedIntegerFunction_sound accepted unique typed ledger valid

/-- Arbitrary existing cells need only satisfy the actual compiler environment
lookups. No whole-heap typing or erased runtime correspondence is assumed. -/
theorem actual_statements_source
    {program : Program} {context finalTyped : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {solved : List SolvedRequirement} {actual : Staged.Environment}
    {environment : Dynamic.Environment} {before : Dynamic.Heap} {fuel : Nat}
    {site : ErrorSite} {reason : ErrorReason} {roots : List StatementId}
    {result : StagedIntegerEvaluation} {control : ControlContext} {facts : BodyFacts}
    (accepted : Staged.Statements.evaluate solved source actual true fuel site reason roots = .ok result)
    (unique : NodeOccurrencesUnique source)
    (typed : StatementsHaveType source control context roots finalTyped facts)
    (ledger : context.solvedRequirements = solved)
    (environments : EnvironmentRep actual environment before)
    (valid : UsedValid context solved result.consumedRequirements) :
    Staged.Statements.Checked solved source actual true fuel roots result ∧
      ∃ final after added,
        Dynamic.StatementsExecute program context evidence source environment before roots final
          (.returned (.integer result.value)) after ∧ Extends before after added :=
  statements_of_accepted accepted unique typed ledger environments valid

theorem original_cell {before after : Dynamic.Heap} {values : List Int}
    {location : Dynamic.Location} {cell : Dynamic.Cell}
    (extension : Extends before after values) (read : Dynamic.Heap.Reads before location cell) :
    Dynamic.Heap.Reads after location cell := extension.preserves_read read

theorem ordered_input_cells {source : TypedSource} {binders : List TypedBinder}
    {values : List Int} {actual : Staged.Environment}
    (accepted : Staged.Statements.bindInputs source [] binders values = .ok actual)
    (before : Dynamic.Heap) :
    ∃ environment after,
      Dynamic.BindersAllocate [] before binders (values.map Dynamic.Value.integer) environment after ∧
      EnvironmentRep actual environment after ∧ Extends before after values :=
  allocate (Staged.Statements.inputs_checked accepted) before

/-- Nonempty input allocation makes the source heap strictly longer. -/
theorem nonempty_inputs_grow {before after : Dynamic.Heap} {arguments added : List Int}
    (nonempty : arguments ≠ []) (extension : Extends before after (arguments ++ added)) :
    before.cells.length < after.cells.length := by
  have length := extension.length_eq
  have positive : 0 < arguments.length := List.length_pos_iff.mpr nonempty
  simp only [List.length_append] at length
  omega

end SourceMeaning

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def content : String := String.intercalate "\n" [
  "function sequential(first: integer, second: integer) returns (integer) {",
  "  let x: integer = integerSub(first, second);",
  "  let y: integer = integerMul(x, 2);",
  "  return integerAdd(y, first);",
  "}",
  "function branch(comptime x: integer) returns (comptime<integer>) {",
  "  if (integerLt(x, 0)) {",
  "    let negative: integer = integerSub(0, x);",
  "    return integerAdd(negative, 3);",
  "  } else {",
  "    let positive: integer = integerAdd(x, 5);",
  "    return integerMul(positive, 2);",
  "  }",
  "}",
  "function nested() returns (integer) {",
  "  let outer: integer = 4;",
  "  { let inner: integer = integerAdd(outer, 6); return inner; }",
  "}",
  "function duplicate() returns (integer) { return integerAdd(3, 4); }",
  "function direct(x: integer) returns (integer) { return sequential(x, x); }"
]

private def named (program : CheckedProgram) (name : String) : IO CheckedFunction :=
  match program.functions.find? fun function =>
      (program.environment.declaration? function.declaration).any fun entry => entry.name == some name with
  | some function => pure function
  | none => throw (IO.userError s!"missing function {name}")

private def roots (function : CheckedFunction) : IO (List StatementId) :=
  function.typedBody.roots.mapM fun
    | .statement statement => pure statement
    | .expression _ => throw (IO.userError "unexpected expression root")

private def evaluate (function : CheckedFunction) (arguments : List Int) (execute : Bool := true) :
    IO StagedIntegerEvaluation := do
  let environment ← match Staged.Statements.bindInputs function.typedBody [] function.typedBody.inputs arguments with
    | .ok environment => pure environment
    | .error error => throw (IO.userError s!"input binding rejected: {reprStr error}")
  let statements ← roots function
  match Staged.Statements.evaluate function.solvedRequirements function.typedBody environment execute
      (function.typedBody.nodes.length + 1) (.declaration function.declaration)
      .statementListFallthrough statements with
  | .ok result => pure result
  | .error error => throw (IO.userError s!"statement evaluation rejected: {reprStr error}")

private def inspect (function : CheckedFunction) (arguments : List Int) (expected : Int) : IO Unit := do
  let result ← evaluate function arguments
  assertTrue (result.value == expected) "actual statement value changed"
  assertTrue (result.consumedRequirements == function.solvedRequirements.map (·.id))
    "statement consumption lost source order or an unselected branch"
  match evaluateStagedIntegerFunction function arguments with
  | .ok value => assertTrue (value == expected) "public function result changed"
  | .error error => throw (IO.userError s!"public function rejected: {reprStr error}")
  let disabled ← evaluate function arguments false
  assertTrue (disabled.consumedRequirements == result.consumedRequirements)
    "disabled statement validation lost consumption"

private def rejected (function : CheckedFunction) (arguments : List Int) : IO Unit :=
  match evaluateStagedIntegerFunction function arguments with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "tampered or unsupported function accepted")

/-- Actual checker output is tested separately from explicitly modified IR. -/
def run : IO Unit := do
  let program ← match checkProgram {
      entry := "main.solc", mainSources := [{ path := "main.solc", content := "pragma solcore;\n" ++ content }], externalLibraries := [] } with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"statement fixture check failed: {reprStr errors}")
  let sequential ← named program "sequential"
  let branch ← named program "branch"
  let nested ← named program "nested"
  let duplicate ← named program "duplicate"
  let direct ← named program "direct"
  inspect sequential [9, 2] 23
  inspect branch [-4] 7
  inspect branch [4] 18
  inspect nested [] 10
  inspect duplicate [] 7
  rejected direct [1]
  rejected sequential [9]
  let inputs := sequential.typedBody.inputs
  match inputs with
  | first :: second :: [] =>
      assertTrue (first.id != second.id && first.scheme.body == Ty.integer && second.scheme.body == Ty.integer)
        "checker input order or type changed"
      rejected { sequential with typedBody := { sequential.typedBody with inputs := [first, first] } } [9, 2]
  | _ => throw (IO.userError "expected two ordered inputs")
  let branchRoots ← roots branch
  let branchStatement ← match branchRoots with
    | [statement] => pure statement
    | _ => throw (IO.userError "branch roots changed")
  let elseBody ← match branch.typedBody.lookupStatement? branchStatement with
    | some { form := .ifThen _ _ (some body), .. } => pure body
    | _ => throw (IO.userError "terminal conditional changed")
  let last ← match elseBody.getLast? with
    | some statement => pure statement
    | none => throw (IO.userError "else branch vanished")
  let invalid := { branch with typedBody := { branch.typedBody with nodes := branch.typedBody.nodes.map fun
    | .statement node => if node.id == last then .statement { node with type := .word } else .statement node
    | node => node } }
  rejected invalid [-4]
  let invalidEnv ← match Staged.Statements.bindInputs invalid.typedBody [] invalid.typedBody.inputs [-4] with
    | .ok env => pure env | .error _ => throw (IO.userError "invalid test inputs")
  match Staged.Statements.evaluate invalid.solvedRequirements invalid.typedBody invalidEnv false
      (invalid.typedBody.nodes.length + 1) (.declaration invalid.declaration) .statementListFallthrough branchRoots with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "disabled validation skipped tampered unselected branch")
  -- An unused ledger row survives statement evaluation but public reconciliation rejects it.
  let extra ← match duplicate.solvedRequirements.head? with
    | some row => pure { row with id := ⟨100000⟩ }
    | none => throw (IO.userError "missing numeric row")
  let augmented := { duplicate with solvedRequirements := extra :: duplicate.solvedRequirements ++ [extra] }
  let original ← evaluate duplicate []
  let augmentedResult ← evaluate augmented []
  assertTrue (original == augmentedResult) "unused ledger rows changed statement traversal"
  match evaluateStagedIntegerFunction augmented [] with
  | .error { reason := .unconsumedRequirements remaining, .. } =>
      assertTrue (remaining == [extra.id, extra.id]) "unused full ledger order changed"
  | _ => throw (IO.userError "public reconciliation lost exact unused ledger rows")
  -- Repeated references are modified retained IR, not fresh checker output.
  let (call, callee, left) ← match duplicate.typedBody.nodes.filterMap (fun
      | .expression node => match node.form with
        | .call callee [left, _] (.builtinFunction .integerAdd) => some (node, callee, left)
        | _ => none
      | _ => none) with
    | [selected] => pure selected
    | _ => throw (IO.userError "duplicate fixture call changed")
  let requirement ← match duplicate.typedBody.lookupExpression? left with
    | some { form := .integerLiteral _ resolution, .. } => pure resolution.requirement
    | _ => throw (IO.userError "duplicate fixture literal changed")
  let repeated := { duplicate with typedBody := { duplicate.typedBody with nodes := duplicate.typedBody.nodes.map fun
    | .expression node => if node.id == call.id then
        .expression { node with form := .call callee [left, left] (.builtinFunction .integerAdd) }
      else .expression node
    | node => node } }
  let repeatedResult ← evaluate repeated []
  assertTrue (repeatedResult.value == 6 && repeatedResult.consumedRequirements == [requirement, requirement])
    "actual ordered duplicate consumption changed"
  match evaluateStagedIntegerFunction repeated [] with
  | .error { reason := .duplicateConsumedRequirement actual, .. } =>
      assertTrue (actual == requirement) "public duplicate rejection named a different row"
  | _ => throw (IO.userError "public reconciliation accepted duplicate consumption")
end Tests.SourceCoreStagedIntegerStatementsMeaning
end

section
-- leanmerge: from Solcore.Test.SourceCoreElaboration
/-! End-to-end and malformed-carrier regressions for the first typed-source to
Semantic Core elaboration profile. -/

set_option autoImplicit false

namespace Tests.SourceCoreElaboration

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content := "pragma solcore;\n" ++ content }]
  externalLibraries := []
}

private def checkedProgram (content : String) : IO CheckedProgram := do
  match checkProgram (workspace content) with
  | .ok checked => pure checked
  | .error errors =>
      throw (IO.userError s!"source-to-Core fixture failed checking: {reprStr errors}")

private def checkedNamed (program : CheckedProgram) (name : String) :
    IO CheckedFunction :=
  match program.functions.find? fun function =>
      match program.environment.declaration? function.declaration with
      | some declaration => declaration.name == some name
      | none => false with
  | some function => pure function
  | none => throw (IO.userError s!"checked function `{name}` was not found")

private def word (value : Nat) : Core.Word :=
  ⟨value % Core.wordModulus, Nat.mod_lt _ (by simp [Core.wordModulus])⟩

private def rootIds (function : CheckedFunction) :
    IO (StatementId × ExpressionId) :=
  match function.typedBody.roots with
  | [.statement statement] =>
      match function.typedBody.lookupStatement? statement with
      | some { form := .returnStmt (some expression), .. } =>
          pure (statement, expression)
      | _ => throw (IO.userError "fixture root is not a valued return")
  | _ => throw (IO.userError "fixture does not have one statement root")

private def changeExpression (source : TypedSource) (id : ExpressionId)
    (change : ExpressionNode → ExpressionNode) : TypedSource := {
  source with
  nodes := source.nodes.map fun
    | .expression node =>
        if node.id = id then .expression { change node with id }
        else .expression node
    | .statement node => .statement node
}

private def changeStatement (source : TypedSource) (id : StatementId)
    (change : StatementNode → StatementNode) : TypedSource := {
  source with
  nodes := source.nodes.map fun
    | .expression node => .expression node
    | .statement node =>
        if node.id = id then .statement { change node with id }
        else .statement node
}

private def withExpression (function : CheckedFunction) (id : ExpressionId)
    (change : ExpressionNode → ExpressionNode) : CheckedFunction := {
  function with typedBody := changeExpression function.typedBody id change
}

private def expectError (label : String) (function : CheckedFunction)
    (site : SourceCoreElaboration.ErrorSite)
    (accept : SourceCoreElaboration.ErrorReason → Bool) : IO Unit := do
  match SourceCoreElaboration.elaborateFunction function with
  | .ok _ => throw (IO.userError s!"{label}: malformed typed source lowered")
  | .error error =>
      assertTrue (decide (error.site = site) && accept error.reason)
        s!"{label}: wrong elaboration error {reprStr error}"

private def testEndToEnd : IO CheckedFunction := do
  let program ← checkedProgram (String.intercalate "\n" [
    "function lower(flag: Bool, x: Word) returns (Word, Bool) {",
    "  return (((flag ? ((x + 1) * 2) : ~x), !(x < 10) || false));",
    "}",
    "function empty() { return; }"
  ])
  let function ← checkedNamed program "lower"
  let lowered ← match SourceCoreElaboration.elaborateFunction function with
    | .ok lowered => pure lowered
    | .error error => throw (IO.userError
        s!"checked builtin function did not lower: {reprStr error}")
  assertTrue (decide (lowered.inputs.values = [.bool, .word] ∧
      lowered.returnType = .product .word .bool ∧
      Core.infer? lowered.inputs.values lowered.core = some lowered.returnType))
    "open Core context or independently inferred return type changed"
  assertTrue (decide (Core.runStateful 100
      (.initial lowered.core [.bool true, .word (word 3)]) =
        .done (.pair (.word (word 8)) (.bool false)) []))
    "lowered open Core expression did not execute to the source result"
  let empty ← checkedNamed program "empty"
  match SourceCoreElaboration.elaborateFunction empty with
  | .ok lowered =>
      assertTrue (decide (lowered.returnType = .unit ∧ lowered.core = .unit))
        "empty return did not lower to Core Unit"
  | .error error => throw (IO.userError
      s!"empty return did not lower: {reprStr error}")
  pure function

private def testStatementLowering : IO Unit := do
  let program ← checkedProgram (String.intercalate "\n" [
    "function statements(flag: Bool, x: Word) returns (Word) {",
    "  {",
    "    let base: Word = x + 1;",
    "    let base: Word = base * 2;",
    "    if (flag) {",
    "      return base + 10;",
    "    } else {",
    "      return x + 20;",
    "    }",
    "  }",
    "}"
  ])
  let function ← checkedNamed program "statements"
  let lowered ← match SourceCoreElaboration.elaborateFunction function with
    | .ok lowered => pure lowered
    | .error error => throw (IO.userError
        s!"checked statement body did not lower: {reprStr error}")
  assertTrue (decide (lowered.inputs.values = [.bool, .word] ∧
      lowered.returnType = .word ∧
      Core.infer? lowered.inputs.values lowered.core = some .word))
    "statement lowering changed its open Core context or result type"
  assertTrue (decide (Core.runStateful 200
      (.initial lowered.core [.bool true, .word (word 3)]) =
        .done (.word (word 18)) []))
    "true tail-if branch lost initialized lets, shadowing, or input lookup"
  assertTrue (decide (Core.runStateful 200
      (.initial lowered.core [.bool false, .word (word 3)]) =
        .done (.word (word 23)) []))
    "false tail-if branch lost its outer input reference"

private def testUninitializedLetRejected : IO Unit := do
  let program ← checkedProgram (String.intercalate "\n" [
    "function uninitialized(x: Word) returns (Word) {",
    "  let pending: Word;",
    "  return pending;",
    "}"
  ])
  let function ← checkedNamed program "uninitialized"
  let statement ← match function.typedBody.roots with
    | .statement statement :: _ => pure statement
    | _ => throw (IO.userError
        "uninitialized-let fixture lost its first statement root")
  expectError "uninitialized let" function
    (.occurrence statement.occurrence)
    fun reason => reason matches .uninitializedLet

private def testRequirementsAndCoercions (function : CheckedFunction) : IO Unit := do
  let (_, expression) ← rootIds function
  let requirement : RequirementId := ⟨37⟩
  let required := withExpression function expression fun node => {
    node with requirements := [requirement]
  }
  expectError "requirement" required (.occurrence expression.occurrence)
    fun reason => match reason with
      | .requirementsPresent [id] => id == requirement
      | _ => false
  let coerced := withExpression function expression fun node => {
    node with
    requirements := [requirement]
    coercions := [{
      requirement
      source := .word
      target := node.type
    }]
  }
  expectError "coercion" coerced (.occurrence expression.occurrence)
    fun reason => match reason with
      | .coercionsPresent [_] => true
      | _ => false

private def requiredWordBinaryPolicy (consumed : List RequirementId) :
    SourceCoreElaboration.RequiredBinaryElaborator
      SourceCoreElaboration.Error :=
  fun _ _ _ _ _ => pure {
    leftType := .word
    rightType := .word
    consumedRequirements := consumed
    build := fun left right => pure (.binary .wordAdd left right)
  }

private def requiredWordUnaryPolicy (consumed : List RequirementId) :
    SourceCoreElaboration.RequiredUnaryElaborator
      SourceCoreElaboration.Error :=
  fun _ _ _ _ => pure {
    operandType := .word
    consumedRequirements := consumed
    build := fun operand => pure (.unary .wordNot operand)
  }

private def solvedWordRequirement (declaration : Resolved.DeclarationId)
    (requirement : RequirementId) : SolvedRequirement :=
  let predicate : ProgramPredicate := {
    trait := declaration
    subject := .word
    arguments := []
  }
  {
    id := requirement
    predicate
    evidence := .assumption predicate
  }

private def executableCoercionPolicy :
    SourceCoreElaboration.CoercionElaborator
      SourceCoreElaboration.Error :=
  fun _ node step =>
    match step.source, step.target with
    | .constructor (.builtin .word), .constructor (.builtin .bool) =>
        pure {
          sourceType := .word
          targetType := .bool
          consumedRequirements := step.requirements
          build := fun value => pure
            (.unary .boolNot (.binary .wordEq value (.word (word 0))))
        }
    | .constructor (.builtin .bool), .constructor (.builtin .word) =>
        pure {
          sourceType := .bool
          targetType := .word
          consumedRequirements := step.requirements
          build := fun value => pure
            (.ifE value (.word (word 1)) (.word (word 0)))
        }
    | _, _ => throw {
        site := .occurrence node.id.occurrence
        reason := .unsupportedType step.source
      }

private def constantCoercionPolicy (sourceType targetType : Core.Ty)
    (consumed : List RequirementId) :
    SourceCoreElaboration.CoercionElaborator
      SourceCoreElaboration.Error :=
  fun _ _ _ => pure {
    sourceType
    targetType
    consumedRequirements := consumed
    build := fun value => pure value
  }

private def replaceCoercionPlanRequirements
    (target : RequirementId) (consumed : List RequirementId) :
    SourceCoreElaboration.CoercionElaborator
      SourceCoreElaboration.Error :=
  fun scope node step => do
    let plan ← executableCoercionPolicy scope node step
    pure {
      plan with
      consumedRequirements :=
        if step.requirement = target then consumed
        else plan.consumedRequirements
    }

private def expectCoercionPolicyError (label : String)
    (function : CheckedFunction) (expression : ExpressionId)
    (policy : SourceCoreElaboration.CoercionElaborator
      SourceCoreElaboration.Error)
    (accept : SourceCoreElaboration.ErrorReason → Bool) : IO Unit := do
  match SourceCoreElaboration.lowerFunctionBodyWithAllPolicies id
      SourceCoreElaboration.rejectCalls
      SourceCoreElaboration.rejectRequiredBinaries policy function with
  | .ok _ => throw (IO.userError s!"{label}: malformed coercion path lowered")
  | .error error =>
      assertTrue (decide (error.site = .occurrence expression.occurrence) &&
          accept error.reason)
        s!"{label}: wrong coercion error {reprStr error}"

private def testRequiredBinaryPolicy : IO Unit := do
  let program ← checkedProgram
    "function required(x: Word) returns (Word) { return x + 1; }"
  let function ← checkedNamed program "required"
  let (_, expression) ← rootIds function
  let requirement : RequirementId := ⟨101⟩
  let leftover : RequirementId := ⟨102⟩
  let predicate : ProgramPredicate := {
    trait := function.declaration
    subject := .word
    arguments := []
  }
  let required : CheckedFunction := {
    function with
    solvedRequirements := function.solvedRequirements ++ [{
      id := requirement
      predicate
      evidence := .assumption predicate
    }]
    typedBody := changeExpression function.typedBody expression fun node => {
      node with requirements := [requirement]
    }
  }
  expectError "required binary default policy" required
    (.occurrence expression.occurrence)
    fun reason => match reason with
      | .requirementsPresent [actual] => actual == requirement
      | _ => false
  let draft ← match SourceCoreElaboration.lowerFunctionBodyWithPolicies id
      SourceCoreElaboration.rejectCalls
      (requiredWordBinaryPolicy [requirement]) required with
    | .ok draft => pure draft
    | .error error => throw (IO.userError
        s!"required binary policy did not lower: {reprStr error}")
  let lowered ← match draft.finalize with
    | .ok lowered => pure lowered
    | .error error => throw (IO.userError
        s!"required binary policy did not finalize: {reprStr error}")
  assertTrue (decide (Core.runStateful 100
      (.initial lowered.core [.word (word 4)]) =
        .done (.word (word 5)) []))
    "required binary policy changed child order or runtime meaning"
  match SourceCoreElaboration.lowerFunctionBodyWithPolicies id
      SourceCoreElaboration.rejectCalls (requiredWordBinaryPolicy [])
      required with
  | .ok _ => throw (IO.userError
      "required binary policy accepted mismatched requirement identities")
  | .error error =>
      assertTrue (decide (error.site = .occurrence expression.occurrence) &&
          match error.reason with
          | .binaryRequirementsMismatch [expected] [] =>
              expected == requirement
          | _ => false)
        s!"required binary mismatch reported the wrong error: {reprStr error}"
  let withLeftover : CheckedFunction := {
    required with
    solvedRequirements := required.solvedRequirements ++ [{
      id := leftover
      predicate
      evidence := .assumption predicate
    }]
  }
  let leftoverDraft ← match
      SourceCoreElaboration.lowerFunctionBodyWithPolicies id
        SourceCoreElaboration.rejectCalls
        (requiredWordBinaryPolicy [requirement]) withLeftover with
    | .ok draft => pure draft
    | .error error => throw (IO.userError
        s!"required binary leftover failed before finalization: {reprStr error}")
  match leftoverDraft.finalize with
  | .ok _ => throw (IO.userError
      "required binary policy silently discarded an unconsumed requirement")
  | .error error =>
      assertTrue (decide (error.site = .declaration function.declaration) &&
          match error.reason with
          | .unconsumedRequirements [actual] => actual == leftover
          | _ => false)
        s!"required binary leftover reported the wrong error: {reprStr error}"

private def testRequiredUnaryPolicy : IO Unit := do
  let program ← checkedProgram
    "function required(x: Word) returns (Word) { return ~x; }"
  let function ← checkedNamed program "required"
  let (_, expression) ← rootIds function
  let requirement : RequirementId := ⟨111⟩
  let predicate : ProgramPredicate := {
    trait := function.declaration
    subject := .word
    arguments := []
  }
  let required : CheckedFunction := {
    function with
    solvedRequirements := [{
      id := requirement
      predicate
      evidence := .assumption predicate
    }]
    typedBody := changeExpression function.typedBody expression fun node => {
      node with requirements := [requirement]
    }
  }
  expectError "required unary default policy" required
    (.occurrence expression.occurrence)
    fun reason => match reason with
      | .requirementsPresent [actual] => actual == requirement
      | _ => false
  match SourceCoreElaboration.lowerFunctionBodyWithAllPolicies id
      SourceCoreElaboration.rejectCalls
      SourceCoreElaboration.rejectRequiredBinaries
      SourceCoreElaboration.rejectCoercions required with
  | .ok _ => throw (IO.userError
      "required unary crossed the compatibility policy boundary")
  | .error error =>
      assertTrue (decide (error.site = .occurrence expression.occurrence) &&
          match error.reason with
          | .requirementsPresent [actual] => actual == requirement
          | _ => false)
        s!"required unary compatibility rejection changed: {reprStr error}"
  let draft ← match
      SourceCoreElaboration.lowerFunctionBodyWithRuntimePolicies id
        SourceCoreElaboration.rejectCalls
        (requiredWordUnaryPolicy [requirement])
        SourceCoreElaboration.rejectRequiredBinaries
        SourceCoreElaboration.rejectCoercions required with
    | .ok draft => pure draft
    | .error error => throw (IO.userError
        s!"required unary policy did not lower: {reprStr error}")
  let lowered ← match draft.finalize with
    | .ok lowered => pure lowered
    | .error error => throw (IO.userError
        s!"required unary policy did not finalize: {reprStr error}")
  assertTrue (decide (Core.runStateful 100
      (.initial lowered.core [.word (word 4)]) =
        .done (.word (word 4).bitNot) []))
    "required unary policy changed operand traversal or runtime meaning"
  match SourceCoreElaboration.lowerFunctionBodyWithRuntimePolicies id
      SourceCoreElaboration.rejectCalls (requiredWordUnaryPolicy [])
      SourceCoreElaboration.rejectRequiredBinaries
      SourceCoreElaboration.rejectCoercions required with
  | .ok _ => throw (IO.userError
      "required unary policy accepted mismatched requirement identities")
  | .error error =>
      assertTrue (decide (error.site = .occurrence expression.occurrence) &&
          match error.reason with
          | .unaryRequirementsMismatch [expected] [] =>
              expected == requirement
          | _ => false)
        s!"required unary mismatch reported the wrong error: {reprStr error}"

private def testCallAwareCompatibility : IO Unit := do
  let program ← checkedProgram (String.intercalate "\n" [
    "function callee(value: Word) returns (Word) { return value; }",
    "function caller(value: Word) returns (Word) { return callee(value); }"
  ])
  let function ← checkedNamed program "caller"
  let onCall : SourceCoreElaboration.CallElaborator
      SourceCoreElaboration.Error :=
    fun _ node _ _ _ => pure {
      argumentTypes := [.word]
      consumedRequirements := []
      build := fun arguments =>
        match arguments with
        | [argument] => pure argument
        | arguments => throw {
            site := .occurrence node.id.occurrence
            reason := .callArgumentArityMismatch 1 arguments.length
          }
    }
  let draft ← match SourceCoreElaboration.lowerFunctionBodyWith id onCall
      function with
    | .ok draft => pure draft
    | .error error => throw (IO.userError
        s!"call-aware compatibility wrapper did not lower: {reprStr error}")
  let lowered ← match draft.finalize with
    | .ok lowered => pure lowered
    | .error error => throw (IO.userError
        s!"call-aware compatibility wrapper did not finalize: {reprStr error}")
  assertTrue (decide (Core.runStateful 100
      (.initial lowered.core [.word (word 19)]) =
        .done (.word (word 19)) []))
    "call-aware compatibility wrapper changed its custom call semantics"

private def testCoercionPolicy : IO Unit := do
  let program ← checkedProgram
    "function coerced(x: Word) returns (Word) { return x + 1; }"
  let function ← checkedNamed program "coerced"
  let (_, expression) ← rootIds function
  let root ← match function.typedBody.lookupExpression? expression with
    | some node => pure node
    | none => throw (IO.userError "coercion fixture lost its root expression")
  let left ← match root.form with
    | .binary left .add _ => pure left
    | _ => throw (IO.userError "coercion fixture root is not addition")
  let binaryRequirement : RequirementId := ⟨201⟩
  let firstCoercion : RequirementId := ⟨202⟩
  let secondCoercion : RequirementId := ⟨203⟩
  let firstMethod0 : RequirementId := ⟨204⟩
  let firstMethod1 : RequirementId := ⟨205⟩
  let secondMethod : RequirementId := ⟨206⟩
  let solved := function.solvedRequirements ++ [
    solvedWordRequirement function.declaration binaryRequirement,
    solvedWordRequirement function.declaration firstCoercion,
    solvedWordRequirement function.declaration secondCoercion,
    solvedWordRequirement function.declaration firstMethod0,
    solvedWordRequirement function.declaration firstMethod1,
    solvedWordRequirement function.declaration secondMethod
  ]
  let rootCoerced : CheckedFunction := {
    function with
    solvedRequirements := solved
    typedBody := changeExpression function.typedBody expression fun node => {
      node with
      requirements := [
        secondMethod, secondCoercion, binaryRequirement,
        firstMethod1, firstCoercion, firstMethod0
      ]
      coercions := [
        {
          requirement := firstCoercion
          methodRequirements := [firstMethod0, firstMethod1]
          source := .word
          target := .bool
        },
        {
          requirement := secondCoercion
          methodRequirements := [secondMethod]
          source := .bool
          target := .word
        }
      ]
    }
  }
  let rootDraft ← match
      SourceCoreElaboration.lowerFunctionBodyWithAllPolicies id
        SourceCoreElaboration.rejectCalls
        (requiredWordBinaryPolicy [binaryRequirement])
        executableCoercionPolicy rootCoerced with
    | .ok draft => pure draft
    | .error error => throw (IO.userError
        s!"root coercion policy did not lower: {reprStr error}")
  let rootLowered ← match rootDraft.finalize with
    | .ok lowered => pure lowered
    | .error error => throw (IO.userError
        s!"root coercion policy did not finalize: {reprStr error}")
  assertTrue (decide (Core.runStateful 100
      (.initial rootLowered.core [.word (word 4)]) =
        .done (.word (word 1)) []))
    "coercion requirements were removed positionally or plans ran out of order"

  let childCoerced : CheckedFunction := {
    function with
    solvedRequirements := solved
    typedBody :=
      changeExpression
        (changeExpression function.typedBody expression fun node => {
          node with requirements := [binaryRequirement]
        }) left fun node => {
          node with
          requirements := [
            firstMethod1, firstCoercion, secondMethod,
            secondCoercion, firstMethod0
          ]
          coercions := [
            {
              requirement := firstCoercion
              methodRequirements := [firstMethod0, firstMethod1]
              source := .word
              target := .bool
            },
            {
              requirement := secondCoercion
              methodRequirements := [secondMethod]
              source := .bool
              target := .word
            }
          ]
        }
  }
  let childDraft ← match
      SourceCoreElaboration.lowerFunctionBodyWithAllPolicies id
        SourceCoreElaboration.rejectCalls
        (requiredWordBinaryPolicy [binaryRequirement])
        executableCoercionPolicy childCoerced with
    | .ok draft => pure draft
    | .error error => throw (IO.userError
        s!"required-binary child coercion did not lower: {reprStr error}")
  let childLowered ← match childDraft.finalize with
    | .ok lowered => pure lowered
    | .error error => throw (IO.userError
        s!"required-binary child coercion did not finalize: {reprStr error}")
  assertTrue (decide (Core.runStateful 100
      (.initial childLowered.core [.word (word 4)]) =
        .done (.word (word 2)) []))
    "required-binary traversal did not recursively execute child coercions"

private def testMalformedCoercionPolicies : IO Unit := do
  let program ← checkedProgram
    "function identity(x: Word) returns (Word) { return x; }"
  let function ← checkedNamed program "identity"
  let (_, expression) ← rootIds function
  let first : RequirementId := ⟨301⟩
  let second : RequirementId := ⟨302⟩
  let firstMethod : RequirementId := ⟨303⟩
  let secondMethod : RequirementId := ⟨304⟩
  let changed (requirements : List RequirementId)
      (coercions : List CoercionStep) : CheckedFunction :=
    withExpression function expression fun node => {
      node with requirements, coercions
    }
  expectCoercionPolicyError "identity coercion step"
    (changed [first] [{ requirement := first, source := .word, target := .word }])
    expression executableCoercionPolicy fun reason => match reason with
      | .identityCoercionStep 0 actual .word => actual == first
      | _ => false
  expectCoercionPolicyError "discontinuous coercion path"
    (changed [first, second] [
      { requirement := first, source := .word, target := .bool },
      { requirement := second, source := .word, target := .bool }
    ]) expression executableCoercionPolicy fun reason => match reason with
      | .coercionPathDiscontinuity 1 .bool .word => true
      | _ => false
  expectCoercionPolicyError "wrong coercion target"
    (changed [first]
      [{ requirement := first, source := .word, target := .bool }])
    expression executableCoercionPolicy fun reason => match reason with
      | .coercionPathTargetMismatch .word .bool => true
      | _ => false
  expectCoercionPolicyError "missing coercion requirement"
    (changed [first] [
      { requirement := first, source := .word, target := .bool },
      { requirement := second, source := .bool, target := .word }
    ]) expression executableCoercionPolicy fun reason => match reason with
      | .missingCoercionRequirement actual [attached] =>
          actual == second && attached == first
      | _ => false
  expectCoercionPolicyError "duplicate coercion requirement"
    (changed [first] [
      { requirement := first, source := .word, target := .bool },
      { requirement := first, source := .bool, target := .word }
    ]) expression executableCoercionPolicy fun reason => match reason with
      | .duplicateCoercionRequirement actual => actual == first
      | _ => false
  let methodStep : CoercionStep := {
    requirement := first
    methodRequirements := [firstMethod, secondMethod]
    source := .word
    target := .bool
  }
  let returnStep : CoercionStep := {
    requirement := second
    source := .bool
    target := .word
  }
  expectCoercionPolicyError "missing coercion method requirement"
    (changed [first, firstMethod, second] [methodStep, returnStep])
    expression executableCoercionPolicy fun reason => match reason with
      | .missingCoercionRequirement actual attached =>
          actual == secondMethod &&
            attached == [first, firstMethod, second]
      | _ => false
  expectCoercionPolicyError "duplicate coercion method requirement"
    (changed [first, firstMethod, second] [
      { methodStep with
        methodRequirements := [firstMethod, firstMethod] },
      returnStep
    ]) expression executableCoercionPolicy fun reason => match reason with
      | .duplicateCoercionRequirement actual => actual == firstMethod
      | _ => false
  let validWithMethods := changed
    [first, firstMethod, secondMethod, second] [methodStep, returnStep]
  let expectedMethodRequirements := [first, firstMethod, secondMethod]
  expectCoercionPolicyError "coercion plan missing method requirement"
    validWithMethods expression
      (replaceCoercionPlanRequirements first [first, firstMethod])
    fun reason => match reason with
      | .coercionPlanRequirementsMismatch actual expected consumed =>
          actual == first && expected == expectedMethodRequirements &&
            consumed == [first, firstMethod]
      | _ => false
  expectCoercionPolicyError "coercion plan duplicate method requirement"
    validWithMethods expression
      (replaceCoercionPlanRequirements first
        [first, firstMethod, secondMethod, secondMethod])
    fun reason => match reason with
      | .coercionPlanRequirementsMismatch actual expected consumed =>
          actual == first && expected == expectedMethodRequirements &&
            consumed == [first, firstMethod, secondMethod, secondMethod]
      | _ => false
  expectCoercionPolicyError "coercion plan reordered method requirements"
    validWithMethods expression
      (replaceCoercionPlanRequirements first
        [first, secondMethod, firstMethod])
    fun reason => match reason with
      | .coercionPlanRequirementsMismatch actual expected consumed =>
          actual == first && expected == expectedMethodRequirements &&
            consumed == [first, secondMethod, firstMethod]
      | _ => false
  expectCoercionPolicyError "coercion plan consumed only primary requirement"
    validWithMethods expression
      (replaceCoercionPlanRequirements first [first])
    fun reason => match reason with
      | .coercionPlanRequirementsMismatch actual expected consumed =>
          actual == first && expected == expectedMethodRequirements &&
            consumed == [first]
      | _ => false
  let valid := changed [first, second] [
    { requirement := first, source := .word, target := .bool },
    { requirement := second, source := .bool, target := .word }
  ]
  expectCoercionPolicyError "coercion plan source"
    valid expression (constantCoercionPolicy .bool .bool [first])
    fun reason => match reason with
      | .coercionPlanSourceTypeMismatch actual .word .bool => actual == first
      | _ => false
  expectCoercionPolicyError "coercion plan target"
    valid expression (constantCoercionPolicy .word .word [first])
    fun reason => match reason with
      | .coercionPlanTargetTypeMismatch actual .bool .word => actual == first
      | _ => false
  expectCoercionPolicyError "coercion plan requirements"
    valid expression (constantCoercionPolicy .word .bool [])
    fun reason => match reason with
      | .coercionPlanRequirementsMismatch actual [expected] [] =>
          actual == first && expected == first
      | _ => false

private def testUnsupportedExpressions (function : CheckedFunction) : IO Unit := do
  let (_, expression) ← rootIds function
  let cases : List
      (String × ExpressionForm × SourceCoreElaboration.UnsupportedExpression) := [
    ("call", .call expression [] (.indirect {
      argumentCount := 0
      argumentTypeBeforeCoercion := .unit
      argumentTypeAfterCoercion := .unit
    }), .call),
    ("lambda", .lambda [] .word [], .lambda),
    ("proxy", .proxy .word, .proxy),
    ("index", .index expression expression, .index)
  ]
  for (label, form, expected) in cases do
    let changed := withExpression function expression fun node => {
      node with form
    }
    expectError label changed (.occurrence expression.occurrence)
      fun reason => match reason with
        | .unsupportedExpression actual => actual == expected
        | _ => false

private def testBrokenEdges (function : CheckedFunction) : IO Unit := do
  let (statement, _) ← rootIds function
  let missingOccurrence : OccurrenceId := {
    owner := function.declaration
    index := function.typedBody.nodes.length + 100
  }
  let missing : ExpressionId := ⟨missingOccurrence⟩
  let missingFunction : CheckedFunction := {
    function with
    typedBody := changeStatement function.typedBody statement fun node => {
      node with form := .returnStmt (some missing)
    }
  }
  expectError "missing child" missingFunction (.occurrence missingOccurrence)
    fun reason => reason matches .missingNode
  let wrongCategory : ExpressionId := ⟨statement.occurrence⟩
  let wrongFunction : CheckedFunction := {
    function with
    typedBody := changeStatement function.typedBody statement fun node => {
      node with form := .returnStmt (some wrongCategory)
    }
  }
  expectError "wrong child category" wrongFunction
    (.occurrence statement.occurrence)
    fun reason => reason matches .expectedExpressionNode

private def testUnsupportedTypesAndDuplicateInputs
    (function : CheckedFunction) : IO Unit := do
  let input ← match function.typedBody.inputs with
    | input :: _ => pure input
    | [] => throw (IO.userError "lowering fixture lost its inputs")
  let variants : List (String × TypeSystem.Ty ×
      (SourceCoreElaboration.ErrorReason → Bool)) := [
    ("flexible variable", .variable ⟨91⟩, fun reason =>
      reason matches .flexibleTypeVariable _),
    ("rigid parameter", .parameter ⟨function.declaration, 7⟩, fun reason =>
      reason matches .rigidTypeParameter _),
    ("nominal", .constructor (.declaration function.declaration), fun reason =>
      reason matches .nominalType _)
  ]
  for (label, type, accepts) in variants do
    let changedInput := { input with scheme := .mono type }
    let changed : CheckedFunction := {
      function with typedBody := {
        function.typedBody with
        inputs := changedInput :: function.typedBody.inputs.tail
      }
    }
    expectError label changed (.binder input.id) accepts
  let duplicate : CheckedFunction := {
    function with typedBody := {
      function.typedBody with
      inputs := input :: function.typedBody.inputs
    }
  }
  expectError "duplicate input" duplicate (.binder input.id)
    fun reason => reason matches .duplicateInput _

private def testTypeMismatchAndUnconsumedRequirement
    (function : CheckedFunction) : IO Unit := do
  let (_, expression) ← rootIds function
  let mismatched := withExpression function expression fun node => {
    node with type := .bool
  }
  expectError "typed root mismatch" mismatched (.occurrence expression.occurrence)
    fun reason => reason matches .typedNodeTypeMismatch _ _
  let predicate : ProgramPredicate := {
    trait := function.declaration
    subject := .word
    arguments := []
  }
  let unconsumed : CheckedFunction := {
    function with
    solvedRequirements := function.solvedRequirements ++ [{
      id := ⟨73⟩
      predicate
      evidence := .assumption predicate
    }]
  }
  expectError "unconsumed requirement" unconsumed
    (.declaration function.declaration)
    fun reason => match reason with
      | .unconsumedRequirements [⟨73⟩] => true
      | _ => false

private def testLegacyOverflowLiteralRejected : IO Unit := do
  let program ← checkedProgram
    "function overflow() returns (Word) { return 115792089237316195423570985008687907853269984665640564039457584007913129639936; }"
  let function ← checkedNamed program "overflow"
  let (_, expression) ← rootIds function
  let source ← match function.typedBody.lookupExpression? expression with
    | some { form := .integerLiteral source _, .. } => pure source
    | _ => throw (IO.userError
        "legacy overflow fixture lost its inferred integer carrier")
  let legacy : CheckedFunction := {
    (withExpression function expression fun node => {
      node with form := .literal source, requirements := []
    }) with solvedRequirements := []
  }
  expectError "legacy overflow literal" legacy
    (.occurrence expression.occurrence)
    fun reason => reason matches .invalidWordLiteral _

private def testStagedIntegerTypeRejected : IO Unit := do
  let program ← checkedProgram
    "function staged(value: integer) returns (integer) { return value; }"
  let function ← checkedNamed program "staged"
  let input ← match function.typedBody.inputs with
    | [input] => pure input
    | inputs => throw (IO.userError
        s!"staged integer fixture has {inputs.length} inputs")
  assertTrue (decide (input.scheme.body = TypeSystem.Ty.integer ∧
      function.inferredBodyType = TypeSystem.Ty.integer))
    "integer did not survive source checking as a distinct staged type"
  expectError "staged integer" function (.binder input.id)
    fun reason => reason == .unsupportedType TypeSystem.Ty.integer
  let literalProgram ← checkedProgram
    "function stagedLiteral() returns (integer) { return 1; }"
  let literalFunction ← checkedNamed literalProgram "stagedLiteral"
  assertTrue (literalFunction.solvedRequirements.any fun solved =>
      solved.predicate == ProgramSignatures.builtinIntPredicate .integer &&
        match solved.evidence with
        | .implementation (.byImpl goal (.builtin .intInteger) []) =>
            goal == solved.predicate
        | _ => false)
    "integer literal did not retain its builtin Int<integer> evidence"
  expectError "staged integer literal" literalFunction
    (.declaration literalFunction.declaration)
    fun reason => reason == .unsupportedType TypeSystem.Ty.integer
  let operatorProgram ← checkedProgram (String.intercalate "\n" [
    "function acceptInteger(value: integer) returns (integer) { return value; }",
    "function directStaged() returns (integer) { return 1 + 1; }",
    "function stagedOperator() returns (integer) {",
    "  return acceptInteger(1 + 1);",
    "}"
  ])
  let validateStagedOperator (label name : String) : IO Unit := do
    let operatorFunction ← checkedNamed operatorProgram name
    assertTrue (operatorFunction.solvedRequirements.length == 2 &&
        operatorFunction.solvedRequirements.all fun solved =>
          solved.predicate == ProgramSignatures.builtinIntPredicate .integer &&
            match solved.evidence with
            | .implementation (.byImpl goal (.builtin .intInteger) []) =>
                goal == solved.predicate
            | _ => false)
      s!"{label} did not retain both Int<integer> solutions"
    assertTrue (operatorFunction.typedBody.nodes.any fun
        | .expression { type := .integer, form := .binary _ .add _, .. } => true
        | _ => false)
      s!"{label} did not retain its integer typed-IR target"
    expectError label operatorFunction
      (.declaration operatorFunction.declaration)
      fun reason => reason == .unsupportedType TypeSystem.Ty.integer
  validateStagedOperator "direct staged integer operator" "directStaged"
  validateStagedOperator "nested staged integer operator" "stagedOperator"

private def intPredicate (target : TypeSystem.Ty) : ProgramPredicate :=
  ProgramSignatures.builtinIntPredicate target

private def intEvidence (target : TypeSystem.Ty)
    (implementation : ProgramImplId := .builtin .intWord)
    (premises : List TypedTraitResolution.Evidence := []) :
    PredicateEvidence :=
  .implementation (.byImpl (intPredicate target) implementation premises)

private def checkedLiteralCarrier (spelling : String) (rawValue : Nat) :
    IO (CheckedFunction × ExpressionId × Syntax.CoreLiteralValue ×
      IntegerLiteralResolution) := do
  let program ← checkedProgram
    ("function literal() returns (Word) { return " ++ spelling ++ "; }")
  let function ← checkedNamed program "literal"
  let (_, expression) ← rootIds function
  let node ← match function.typedBody.lookupExpression? expression with
    | some node => pure node
    | none => throw (IO.userError
        "checked integer-literal fixture lost its expression node")
  let (source, resolution) ← match node.form with
    | .integerLiteral source resolution =>
        if node.type == TypeSystem.Ty.word &&
            resolution.rawValue == rawValue &&
            resolution.targetType == TypeSystem.Ty.word &&
            node.requirements == [resolution.requirement] then
          pure (source, resolution)
        else
          throw (IO.userError
            "inferred integer carrier metadata does not match its source")
    | _ => throw (IO.userError
        "checked integer-literal fixture lost its inferred carrier")
  assertTrue (function.solvedRequirements == [{
      id := resolution.requirement
      predicate := resolution.predicate
      evidence := intEvidence .word
    }])
    "inferred integer carrier lost its exact builtin Int<Word> solution"
  pure (function, expression, source, resolution)

private def expectIntegerLiteralError (label : String)
    (function : CheckedFunction) (expression : ExpressionId)
    (accept : SourceCoreElaboration.ErrorReason → Bool) : IO Unit :=
  expectError label function (.occurrence expression.occurrence) accept

private def testIntegerLiteralCarrierExecution : IO Unit := do
  let modulusSpelling :=
    "115792089237316195423570985008687907853269984665640564039457584007913129639936"
  let (zeroFunction, _, _, _) ←
    checkedLiteralCarrier modulusSpelling Core.wordModulus
  let zero ← match SourceCoreElaboration.elaborateFunction zeroFunction with
    | .ok lowered => pure lowered
    | .error error => throw (IO.userError
        s!"2^256 integer carrier did not lower: {reprStr error}")
  assertTrue (decide (zero.resolved = .word (word 0) ∧
      zero.core = .word (word 0) ∧
      Core.runStateful 8 (.initial zero.core []) =
        .done (.word (word 0)) []))
    "Int.fromInteger Word projection did not reduce 2^256 modulo 2^256"
  let successorSpelling :=
    "115792089237316195423570985008687907853269984665640564039457584007913129639937"
  let (oneFunction, _, _, _) ←
    checkedLiteralCarrier successorSpelling (Core.wordModulus + 1)
  let one ← match SourceCoreElaboration.elaborateFunction oneFunction with
    | .ok lowered => pure lowered
    | .error error => throw (IO.userError
        s!"2^256+1 integer carrier did not lower: {reprStr error}")
  assertTrue (decide (one.resolved = .word (word 1) ∧
      one.core = .word (word 1) ∧
      Core.runStateful 8 (.initial one.core []) =
        .done (.word (word 1)) []))
    "Int.fromInteger Word projection did not reduce 2^256+1 to one"
  let hexadecimalSpelling :=
    "0x1" ++ String.intercalate "" (List.replicate 64 "0")
  let (hexadecimalFunction, _, _, _) ←
    checkedLiteralCarrier hexadecimalSpelling Core.wordModulus
  let hexadecimal ←
      match SourceCoreElaboration.elaborateFunction hexadecimalFunction with
    | .ok lowered => pure lowered
    | .error error => throw (IO.userError
        s!"hexadecimal 2^256 integer carrier did not lower: {reprStr error}")
  assertTrue (decide (hexadecimal.resolved = .word (word 0) ∧
      hexadecimal.core = .word (word 0) ∧
      Core.runStateful 8 (.initial hexadecimal.core []) =
        .done (.word (word 0)) []))
    "hexadecimal Int.fromInteger carrier did not reduce 2^256 modulo 2^256"

private def testIntegerLiteralCoercionComposition : IO Unit := do
  let (function, expression, _, resolution) ←
    checkedLiteralCarrier "17" 17
  let (statement, _) ← rootIds function
  let coercionRequirement : RequirementId := ⟨103⟩
  let coercionPredicate : ProgramPredicate := {
    trait := function.declaration
    subject := .word
    arguments := [.bool]
  }
  let coercedExpression := withExpression function expression fun node => {
    node with
    type := .bool
    requirements := [resolution.requirement, coercionRequirement]
    coercions := [{
      requirement := coercionRequirement
      source := .word
      target := .bool
    }]
  }
  let coerced : CheckedFunction := {
    coercedExpression with
    type := .function .unit .bool
    inferredBodyType := .bool
    solvedRequirements := function.solvedRequirements ++ [{
      id := coercionRequirement
      predicate := coercionPredicate
      evidence := .assumption coercionPredicate
    }]
    typedBody := changeStatement coercedExpression.typedBody statement fun node => {
      node with type := .bool
    }
  }
  let draft ← match
      SourceCoreElaboration.lowerFunctionBodyWithAllPolicies id
        SourceCoreElaboration.rejectCalls
        SourceCoreElaboration.rejectRequiredBinaries
        executableCoercionPolicy coerced with
    | .ok draft => pure draft
    | .error error => throw (IO.userError
        s!"integer literal did not compose with its coercion path: {reprStr error}")
  let lowered ← match draft.finalize with
    | .ok lowered => pure lowered
    | .error error => throw (IO.userError
        s!"coerced integer literal did not finalize: {reprStr error}")
  assertTrue (decide (Core.runStateful 16 (.initial lowered.core []) =
      .done (.bool true) []))
    "coercion preparation did not validate the integer carrier at its raw Word type"

private def testMalformedIntegerLiteralCarriers : IO Unit := do
  let (function, expression, source, resolution) ←
    checkedLiteralCarrier "17" 17
  let expected := resolution.predicate
  let solved : SolvedRequirement := {
    id := resolution.requirement
    predicate := expected
    evidence := intEvidence .word
  }
  let changeNode (change : ExpressionNode → ExpressionNode) :=
    withExpression function expression change
  let targetMismatch := changeNode fun node => {
    node with form := .integerLiteral source {
      resolution with targetType := .bool
    }
  }
  expectIntegerLiteralError "integer target/node mismatch" targetMismatch
    expression fun reason =>
      reason == .integerLiteralTargetTypeMismatch .bool .word
  let requirementsMismatch := changeNode fun node => {
    node with requirements := []
  }
  expectIntegerLiteralError "integer requirement attachment"
    requirementsMismatch expression fun reason =>
      reason == .integerLiteralRequirementsMismatch
        [resolution.requirement] []
  let extraRequirement : RequirementId := ⟨102⟩
  let extraRequirements := changeNode fun node => {
    node with requirements := [resolution.requirement, extraRequirement]
  }
  expectIntegerLiteralError "integer extra requirement attachment"
    extraRequirements expression fun reason =>
      reason == .integerLiteralRequirementsMismatch
        [resolution.requirement] [resolution.requirement, extraRequirement]
  let malformedSource := changeNode fun node => {
    node with form := .integerLiteral (.decimal "1x") resolution
  }
  expectIntegerLiteralError "integer source decoding" malformedSource
    expression fun reason => reason ==
      .invalidIntegerLiteralSource (.decimal "1x")
  let rawMismatch := changeNode fun node => {
    node with form := .integerLiteral source {
      resolution with rawValue := 18
    }
  }
  expectIntegerLiteralError "integer decoded value" rawMismatch expression
    fun reason => reason == .integerLiteralRawValueMismatch 17 18
  let missing : CheckedFunction := { function with solvedRequirements := [] }
  expectIntegerLiteralError "integer missing solved row" missing expression
    fun reason => reason ==
      .missingIntegerLiteralRequirement resolution.requirement
  let duplicate : CheckedFunction := {
    function with solvedRequirements := [solved, solved]
  }
  expectIntegerLiteralError "integer duplicate solved row" duplicate expression
    fun reason => reason ==
      .duplicateIntegerLiteralRequirements resolution.requirement 2
  let wrongPredicate := intPredicate .bool
  let predicateMismatch : CheckedFunction := {
    function with solvedRequirements := [{
      solved with predicate := wrongPredicate
    }]
  }
  expectIntegerLiteralError "integer predicate" predicateMismatch expression
    fun reason => reason == .integerLiteralPredicateMismatch
      resolution.requirement expected wrongPredicate
  let evidenceGoalMismatch : CheckedFunction := {
    function with solvedRequirements := [{
      solved with evidence := intEvidence .bool
    }]
  }
  expectIntegerLiteralError "integer evidence goal" evidenceGoalMismatch
    expression fun reason => reason == .integerLiteralEvidenceGoalMismatch
      resolution.requirement expected (intPredicate .bool)
  let assumption : CheckedFunction := {
    function with solvedRequirements := [{
      solved with evidence := .assumption expected
    }]
  }
  expectIntegerLiteralError "integer assumption evidence" assumption expression
    fun reason => reason ==
      .unresolvedIntegerLiteralEvidence resolution.requirement
  let wrongImplementation : ProgramImplId := .builtin .intInteger
  let implementationMismatch : CheckedFunction := {
    function with solvedRequirements := [{
      solved with evidence := intEvidence .word wrongImplementation
    }]
  }
  expectIntegerLiteralError "integer implementation" implementationMismatch
    expression fun reason => reason == .integerLiteralImplementationMismatch
      resolution.requirement (.builtin .intWord) wrongImplementation
  let premise : TypedTraitResolution.Evidence :=
    .byImpl expected (.builtin .intWord) []
  let premisesPresent : CheckedFunction := {
    function with solvedRequirements := [{
      solved with evidence := intEvidence .word (.builtin .intWord) [premise]
    }]
  }
  expectIntegerLiteralError "integer premises" premisesPresent expression
    fun reason => reason == .integerLiteralPremiseCountMismatch
      resolution.requirement 0 1

/-- Exercise the complete first source-to-Core lowering profile and every
staged boundary that must reject explicitly. -/
def testSourceCoreElaboration : IO Unit := do
  let function ← testEndToEnd
  testStatementLowering
  testUninitializedLetRejected
  testRequirementsAndCoercions function
  testRequiredBinaryPolicy
  testRequiredUnaryPolicy
  testCallAwareCompatibility
  testCoercionPolicy
  testMalformedCoercionPolicies
  testUnsupportedExpressions function
  testBrokenEdges function
  testUnsupportedTypesAndDuplicateInputs function
  testTypeMismatchAndUnconsumedRequirement function
  testLegacyOverflowLiteralRejected
  testStagedIntegerTypeRejected
  testIntegerLiteralCarrierExecution
  testIntegerLiteralCoercionComposition
  testMalformedIntegerLiteralCarriers

end Tests.SourceCoreElaboration
end

section
-- leanmerge: from Solcore.Test.SourceCoreUncheckedExecution
/-! `unchecked { … }` blocks through the public source API (solcore-rs #119),
as far as Lean implements them: `+`, `-` and `*` and their compound forms on
Words, which wrap in a block as outside it, `unchecked` as an ordinary name,
blocks in loops, lambdas written in a block, helpers called from one, and the
rejected programs. Unchecked `/` and `%` and their compound forms panic with
`Panic(0x12)` on a zero divisor, also at a mapping element, while checked `/`
and `%` still give 0. Every expected value is what the pinned Rust paths give
(lane D's probe, in `docs/design/integer-types-unchecked-shifts.md`). -/
set_option autoImplicit false
namespace Tests.SourceCoreUncheckedExecution
open Solcore Solcore.Frontend SourceCoreExecution

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def word (n : Nat) : Value := .word (Core.Word.ofNatModulo n)
private def workspaceOf (lines : List String) : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [],
  mainSources := [{path := "main.solc", content := "pragma solcore;\n" ++ String.intercalate "\n" lines}] }

private def maximum : Nat := 2 ^ 256 - 1
private def high : Nat := 2 ^ 255

private def workspace : Workspace.RawWorkspace := workspaceOf [
  "function wrapAdd(x: Word) returns (Word) { unchecked { return x + 1; } }",
  "function wrapSub(x: Word) returns (Word) { let r: Word = 0; unchecked { r = r - x; } return r; }",
  "function wrapMul(x: Word, y: Word) returns (Word) { unchecked { let r: Word = x * y; return r; } }",
  "function compound(x: Word) returns (Word) { let r: Word = x; unchecked { r += 1; r *= 3; r -= 2; } return r; }",
  "function named() returns (Word) { let unchecked: Word = 4; unchecked = unchecked + 1; return unchecked; }",
  "function loop(n: Word) returns (Word) { let total: Word = 0; let i: Word = 0; while (i < n) { unchecked { total = total + i; i = i + 1; } } return total; }",
  "function lambdaDivision(a: Word, b: Word) returns (Word) { unchecked { let divide = lam(x: Word, y: Word) -> Word { return x / y; }; return divide(a, b); } }",
  "function helper(a: Word, b: Word) returns (Word) { return a / b; }",
  "function helperDivision(a: Word, b: Word) returns (Word) { unchecked { return helper(a, b); } }",
  "function lambdaBlock(x: Word) returns (Word) { unchecked { let next = lam(y: Word) -> Word { unchecked { return y + 1; } }; return next(x) * 2; } }",
  "function shadowed(x: Word) returns (Word) { let r: Word = x; unchecked { let r: Word = 7; r = r + 1; } return r; }",
  "function divide(a: Word, b: Word) returns (Word) { unchecked { return a / b; } }",
  "function remainder(a: Word, b: Word) returns (Word) { unchecked { return a % b; } }",
  "function divideAssign(a: Word, b: Word) returns (Word) { let r: Word = a; unchecked { r /= b; } return r; }",
  "function remainderAssign(a: Word, b: Word) returns (Word) { let r: Word = a; unchecked { r %= b; } return r; }",
  "function tableDivide(a: Word, b: Word) returns (Word) { let table: mapping(Word => Word); table[7] = a; unchecked { table[7] /= b; } return table[7]; }",
  "function tableRemainder(a: Word, b: Word) returns (Word) { let table: mapping(Word => Word); table[7] = a; unchecked { table[7] %= b; } return table[7]; }"
]

private def names : List String :=
  ["wrapAdd", "wrapSub", "wrapMul", "compound", "named", "loop", "lambdaDivision",
    "helperDivision", "lambdaBlock", "shadowed", "divide", "remainder", "divideAssign",
    "remainderAssign", "tableDivide", "tableRemainder"]

private def seed (program : CheckedProgram) (name : String) : IO Seed :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure (SourceCoreCompiler.Seed.declaration signature.id)
  | _ => throw (IO.userError s!"unchecked fixture missing {name}")
private def execute {artifact : Artifact} (session : Session artifact) (key : Key) (arguments : List Value) :
    IO (Completion artifact) := do
  let executed ← session.runWithReceipt key arguments {executionFuel := 300000}
  match executed.val with
  | .ok (.succeeded result) => pure result
  | .ok (.exportError error _) => throw (IO.userError s!"unchecked export: {reprStr error}")
  | .ok (.failed reason _) => throw (IO.userError s!"unchecked language failure: {reprStr reason}")
  | .ok (.outOfFuel _) => throw (IO.userError "unchecked execution exhausted")
  | .error error => throw (IO.userError s!"unchecked invocation: {reprStr error}")
/-- A run that fails with `Panic(0x12)`: the reason is the panic's, the
diagnostic decodes it, and the revert data is upstream's. -/
private def panics {artifact : Artifact} (session : Session artifact) (key : Key) (arguments : List Value)
    (label : String) : IO (Session artifact) := do
  let executed ← session.runWithReceipt key arguments {executionFuel := 300000}
  match executed.val with
  | .ok (.failed reason next) =>
      let code := SourceCorePanics.divisionByZero
      require (SourceCorePanics.code? reason == some code) s!"{label} failed with {reprStr reason}"
      match session.diagnostic key reason with
      | .ok (some diagnostic) =>
          require (decide (diagnostic.error = .panic code)) s!"{label} decoded {reprStr diagnostic.error}"
      | other => throw (IO.userError s!"{label} decoded {reprStr other}")
      let data := ((SourceCorePanics.code? reason).map SourceCorePanics.revertData).map ByteArray.toList
      require (data == some ([0x4e, 0x48, 0x7b, 0x71] ++ List.replicate 31 0 ++ [0x12]))
        s!"{label} revert data {reprStr data}"
      pure next
  | .ok (.succeeded result) => throw (IO.userError s!"{label} gave {reprStr result.value}")
  | .ok _ => throw (IO.userError s!"{label} did not fail")
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def boot (artifact : Artifact) : IO (Session artifact) := do
  let fresh ← artifact.bootstrapWithReceipt
  match fresh.val.resume 300000 with
  | .ready session => pure session
  | .error error => throw (IO.userError s!"unchecked bootstrap: {reprStr error}")
  | .outOfFuel _ => throw (IO.userError "unchecked bootstrap exhausted")

private def rejected (label : String) (lines : List String) : IO Unit :=
  match checkProgram (workspaceOf lines) with
  | .ok _ => throw (IO.userError s!"{label} was accepted")
  | .error _ => pure ()

/-- The block's own load error, so that a program is not rejected for an
unrelated reason. -/
private def rejectedWhileLoading (label : String) (expected : Syntax.Unchecked.Error → Bool)
    (lines : List String) : IO Unit :=
  match checkProgram (workspaceOf lines) with
  | .ok _ => throw (IO.userError s!"{label} was accepted")
  | .error [.loading (.uncheckedBlock _ error)] =>
      unless expected error do throw (IO.userError s!"{label} gave {reprStr error}")
  | .error errors => throw (IO.userError s!"{label} gave {reprStr errors}")

/-- Inference itself rejects the program, after loading succeeded. -/
private def rejectedByInference (label : String) (lines : List String) : IO Unit :=
  match checkProgram (workspaceOf lines) with
  | .ok _ => throw (IO.userError s!"{label} was accepted")
  | .error [.inference _] => pure ()
  | .error errors => throw (IO.userError s!"{label} gave {reprStr errors}")

def run : IO Unit := do
  let program ← get "unchecked check" (checkProgram workspace)
  let seeds ← names.mapM (seed program)
  let compiled ← get "unchecked compilation"
    (compile workspace seeds {specializationBudget := 256, compilationFuel := 1000})
  let key (index : Nat) : IO Key := match compiled.keys[index]? with
    | some key => pure key | none => throw (IO.userError "unchecked root missing")
  let mut session ← boot (← compiled.open)
  let cases : List (Nat × List Nat × Nat) :=
    [(0, [5], 6), (0, [maximum], 0),
      (1, [1], maximum), (1, [0], 0),
      (2, [high, 2], 0), (2, [3, 5], 15),
      (3, [maximum], maximum - 1), (3, [4], 13),
      (4, [], 5),
      (5, [4], 6), (5, [0], 0),
      (6, [7, 2], 3), (6, [7, 0], 0),
      (7, [9, 0], 0), (7, [9, 4], 2),
      (8, [maximum], 0), (8, [4], 10),
      (9, [3], 3),
      (10, [7, 2], 3), (11, [7, 2], 1), (12, [9, 4], 2), (13, [9, 4], 1),
      (14, [9, 4], 2), (15, [9, 4], 1)]
  for (index, arguments, expected) in cases do
    let completed ← execute session (← key index) (arguments.map word)
    require (completed.value == word expected)
      s!"unchecked case {names[index]?} {arguments} gave {reprStr completed.value}"
    session := completed.session
  for (index, arguments) in [(10, [7, 0]), (11, [7, 0]), (12, [9, 0]), (13, [9, 0]), (14, [9, 0]), (15, [9, 0])] do
    session ← panics session (← key index) (arguments.map word) s!"unchecked case {names[index]?} {arguments}"
  -- The session survives a panic.
  let completed ← execute session (← key 10) [word 8, word 2]
  require (completed.value == word 4) "unchecked division after a panic"
  rejectedWhileLoading "a block in a block" (fun | .nested _ => true | _ => false)
    ["function bad() returns (Word) { unchecked { unchecked { return 1; } } }"]
  discard <| get "checked integer arithmetic"
    (checkProgram (workspaceOf ["function good(n: integer) returns (integer) { return n + 1; }"]))
  rejectedByInference "unchecked arithmetic on integer"
    ["function bad(n: integer) returns (integer) { unchecked { return n + 1; } }"]
  rejected "a block as an expression"
    ["function bad() returns (Word) { let x: Word = unchecked { 1 }; return x; }"]
  IO.println "SOURCE_CORE_UNCHECKED_PASS: unchecked `+`, `-` and `*` wrap on Words with their compound forms, unchecked `/` and `%` panic with 0x12 on a zero divisor (also compound and at a mapping element), `unchecked` stays a name, blocks reach no lambda body or helper, and nested blocks, unchecked `integer` arithmetic and blocks as expressions are rejected"

end Tests.SourceCoreUncheckedExecution
end

section
/-! The twelve fixed-width integer types through the public source API (row 1's
types step): `uint8` … `uint256` and `int8` … `int256` are builtins, and a value
of one of them is the word that is canonical for the type: below `2^N` for
`uintN`, sign-extended from bit `N - 1` for `intN`. Parameters, results, locals
and mapping elements hold such values, and a missing mapping element is zero.
An argument that is not canonical for its parameter's type is rejected before
the body runs, as upstream's ABI decoder rejects it. The types are distinct
from each other and from `Word`. No operator is defined on them yet, and a
literal at one of them is still rejected; row 1's later steps add both. -/
set_option autoImplicit false
namespace Tests.SourceCoreFixedIntegerTypes
open Solcore Solcore.Frontend SourceCoreExecution

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def word (n : Nat) : Value := .word (Core.Word.ofNatModulo n)
private def workspaceOf (lines : List String) : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [],
  mainSources := [{path := "main.solc", content := "pragma solcore;\n" ++ String.intercalate "\n" lines}] }

private def types : List TypeSystem.FixedInteger := TypeSystem.FixedInteger.all
private def modulus : Nat := 2 ^ 256

/-- Words canonical for the type: zero and its extremes, and `-1` when signed. -/
private def canonicalSamples (type : TypeSystem.FixedInteger) : List Nat :=
  if type.signed then
    [0, 2 ^ (type.width.bits - 1) - 1, modulus - 2 ^ (type.width.bits - 1), modulus - 1]
  else [0, 2 ^ type.width.bits - 1]

/-- Words that are not canonical for the type: just past each extreme. Every
word is canonical for `uint256` and `int256`. -/
private def nonCanonicalSamples (type : TypeSystem.FixedInteger) : List Nat :=
  if type.width.bits = 256 then []
  else if type.signed then [2 ^ (type.width.bits - 1), modulus - 2 ^ (type.width.bits - 1) - 1]
  else [2 ^ type.width.bits, modulus - 1]

private def identity (type : TypeSystem.FixedInteger) : String :=
  "function id" ++ type.name ++ "(x: " ++ type.name ++ ") returns (" ++ type.name ++ ") { return x; }"

private def workspace : Workspace.RawWorkspace := workspaceOf (types.map identity ++ [
  "function store(k: uint8, v: int8) returns (int8) { let table: mapping(uint8 => int8); table[k] = v; return table[k]; }",
  "function missing(k: uint16) returns (int32) { let table: mapping(uint16 => int32); return table[k]; }",
  "function copy(x: int256) returns (int256) { let y: int256 = x; return y; }"
])

private def names : List String := types.map (fun type => "id" ++ type.name) ++ ["store", "missing", "copy"]

private def seed (program : CheckedProgram) (name : String) : IO Seed :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure (SourceCoreCompiler.Seed.declaration signature.id)
  | _ => throw (IO.userError s!"fixed-width fixture missing {name}")
private def execute {artifact : Artifact} (session : Session artifact) (key : Key) (arguments : List Value) :
    IO (Completion artifact) := do
  let executed ← session.runWithReceipt key arguments {executionFuel := 300000}
  match executed.val with
  | .ok (.succeeded result) => pure result
  | .ok (.exportError error _) => throw (IO.userError s!"fixed-width export: {reprStr error}")
  | .ok (.failed reason _) => throw (IO.userError s!"fixed-width language failure: {reprStr reason}")
  | .ok (.outOfFuel _) => throw (IO.userError "fixed-width execution exhausted")
  | .error error => throw (IO.userError s!"fixed-width invocation: {reprStr error}")
/-- The arguments are rejected as not canonical before the body runs. -/
private def rejectedArguments {artifact : Artifact} (session : Session artifact) (key : Key)
    (arguments : List Value) (label : String) : IO Unit := do
  let executed ← session.runWithReceipt key arguments {executionFuel := 300000}
  match executed.val with
  | .error error =>
      require (((reprStr error).splitOn "nonCanonicalSourceValue").length > 1)
        s!"{label} was rejected for another reason: {reprStr error}"
  | .ok _ => throw (IO.userError s!"{label} was accepted")
private def boot (artifact : Artifact) : IO (Session artifact) := do
  let fresh ← artifact.bootstrapWithReceipt
  match fresh.val.resume 300000 with
  | .ready session => pure session
  | .error error => throw (IO.userError s!"fixed-width bootstrap: {reprStr error}")
  | .outOfFuel _ => throw (IO.userError "fixed-width bootstrap exhausted")

/-- Inference itself rejects the program, after loading succeeded. -/
private def rejectedByInference (label : String) (lines : List String) : IO Unit :=
  match checkProgram (workspaceOf lines) with
  | .ok _ => throw (IO.userError s!"{label} was accepted")
  | .error [.inference _] => pure ()
  | .error errors => throw (IO.userError s!"{label} gave {reprStr errors}")

def run : IO Unit := do
  for type in types do
    require ((canonicalSamples type).all type.canonical) s!"{type.name} canonical samples"
    require ((nonCanonicalSamples type).all (!type.canonical ·)) s!"{type.name} non-canonical samples"
  let program ← get "fixed-width check" (checkProgram workspace)
  let seeds ← names.mapM (seed program)
  let compiled ← get "fixed-width compilation"
    (compile workspace seeds {specializationBudget := 256, compilationFuel := 1000})
  let key (index : Nat) : IO Key := match compiled.keys[index]? with
    | some key => pure key | none => throw (IO.userError "fixed-width root missing")
  let mut session ← boot (← compiled.open)
  for (type, index) in types.zipIdx do
    for n in canonicalSamples type do
      let completed ← execute session (← key index) [word n]
      require (completed.value == word n) s!"id{type.name} on {n} gave {reprStr completed.value}"
      session := completed.session
    for n in nonCanonicalSamples type do
      rejectedArguments session (← key index) [word n] s!"id{type.name} on {n}"
  let completed ← execute session (← key 12) [word 5, word (modulus - 3)]
  require (completed.value == word (modulus - 3)) s!"store gave {reprStr completed.value}"
  session := completed.session
  rejectedArguments session (← key 12) [word 256, word 1] "store with key 256"
  rejectedArguments session (← key 12) [word 1, word 128] "store with value 128"
  let completed ← execute session (← key 13) [word 7]
  require (completed.value == word 0) s!"missing gave {reprStr completed.value}"
  session := completed.session
  let completed ← execute session (← key 14) [word (modulus - 5)]
  require (completed.value == word (modulus - 5)) s!"copy gave {reprStr completed.value}"
  rejectedByInference "uint256 is not Word" ["function bad(x: uint256) returns (Word) { return x; }"]
  rejectedByInference "uint8 is not uint16" ["function bad(x: uint8) returns (uint16) { return x; }"]
  rejectedByInference "int8 is not uint8" ["function bad(x: int8) returns (uint8) { return x; }"]
  rejectedByInference "a literal above uint8's range" ["function bad() returns (uint8) { return 256; }"]
  IO.println "SOURCE_CORE_FIXED_TYPES_PASS: the twelve fixed-width integer types as parameters, results, locals and mapping elements hold canonical words, a missing element is zero, non-canonical arguments are rejected before the body runs, the types are distinct from each other and from Word, and a literal above a type's range is rejected"

end Tests.SourceCoreFixedIntegerTypes
end

section
/-! The operators on the twelve fixed-width integer types, through the public
source API: `==`, `!=`, `& | ^`, `< > <= >=`, `~`, checked `+ - * / %` and
their compound forms, and literals at the twelve types. The orderings compare
signed on the signed types, `~` keeps the low `N` bits on the unsigned types
below 256 bits, checked arithmetic panics with `Panic(0x11)` outside the type's
range, and `/ %` panic with `Panic(0x12)` on a zero divisor and round toward
zero, so the results stay canonical. A literal takes the type its uses give it,
and one above the type's greatest value is rejected. A prefix `-` on a literal
folds into it, through groups and repeated, and the range is checked with the
sign; any other `-e` reads as `0 - e`. Unchecked `+ - * / %` wrap to the
type's width (`runUnchecked`), and `<< >>` are Word's shifts read at the
type (`runShifts`), and so are `<<= >>=` (`runCompoundShifts`); in-place `~`
takes the target's type (`runBitNotAssignments`). -/
set_option autoImplicit false
namespace Tests.SourceCoreFixedIntegerOperators
open Solcore Solcore.Frontend SourceCoreExecution

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def word (n : Nat) : Value := .word (Core.Word.ofNatModulo n)
private def boolean (b : Bool) : Value := .bool b
private def workspaceOf (lines : List String) : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [],
  mainSources := [{path := "main.solc", content := "pragma solcore;\n" ++ String.intercalate "\n" lines}] }
private def modulus : Nat := 2 ^ 256

private def workspace : Workspace.RawWorkspace := workspaceOf [
  "function eq8(x: uint8, y: uint8) returns (bool) { return x == y; }",
  "function ne16(x: int16, y: int16) returns (bool) { return x != y; }",
  "function lt32(x: uint32, y: uint32) returns (bool) { return x < y; }",
  "function le64(x: uint64, y: uint64) returns (bool) { return x <= y; }",
  "function gt128(x: uint128, y: uint128) returns (bool) { return x > y; }",
  "function ge256(x: uint256, y: uint256) returns (bool) { return x >= y; }",
  "function and8(x: uint8, y: uint8) returns (uint8) { return x & y; }",
  "function or16(x: uint16, y: uint16) returns (uint16) { return x | y; }",
  "function xor32(x: uint32, y: uint32) returns (uint32) { return x ^ y; }",
  "function eqSigned(x: int256, y: int256) returns (bool) { return x == y; }",
  "function mixed(x: uint8, y: uint8) returns (uint8) { let both: uint8 = x & y; return both | (x ^ y); }",
  "function and8s(x: int8, y: int8) returns (int8) { return x & y; }",
  "function or16s(x: int16, y: int16) returns (int16) { return x | y; }",
  "function xor256s(x: int256, y: int256) returns (int256) { return x ^ y; }",
  "function not8s(x: int8) returns (int8) { return ~x; }",
  "function not256s(x: int256) returns (int256) { return ~x; }",
  "function not256u(x: uint256) returns (uint256) { return ~x; }",
  "function lt8s(x: int8, y: int8) returns (bool) { return x < y; }",
  "function ge16s(x: int16, y: int16) returns (bool) { return x >= y; }",
  "function gt256s(x: int256, y: int256) returns (bool) { return x > y; }",
  "function le32s(x: int32, y: int32) returns (bool) { return x <= y; }",
  "function not8u(x: uint8) returns (uint8) { return ~x; }",
  "function not16u(x: uint16) returns (uint16) { return ~x; }",
  "function not128u(x: uint128) returns (uint128) { return ~x; }",
  "function add8u(x: uint8, y: uint8) returns (uint8) { return x + y; }",
  "function sub16u(x: uint16, y: uint16) returns (uint16) { return x - y; }",
  "function mul32u(x: uint32, y: uint32) returns (uint32) { return x * y; }",
  "function add256u(x: uint256, y: uint256) returns (uint256) { return x + y; }",
  "function mul256u(x: uint256, y: uint256) returns (uint256) { return x * y; }",
  "function add8s(x: int8, y: int8) returns (int8) { return x + y; }",
  "function sub8s(x: int8, y: int8) returns (int8) { return x - y; }",
  "function mul8s(x: int8, y: int8) returns (int8) { return x * y; }",
  "function sub256s(x: int256, y: int256) returns (int256) { return x - y; }",
  "function mul256s(x: int256, y: int256) returns (int256) { return x * y; }",
  "function addAssign8u(x: uint8, y: uint8) returns (uint8) { let r: uint8 = x; r += y; return r; }",
  "function subAssign8u(x: uint8, y: uint8) returns (uint8) { let r: uint8 = x; r -= y; return r; }",
  "function mulAssign8u(x: uint8, y: uint8) returns (uint8) { let r: uint8 = x; r *= y; return r; }",
  "function addAssign256u(x: uint256, y: uint256) returns (uint256) { let r: uint256 = x; r += y; return r; }",
  "function subAssign256u(x: uint256, y: uint256) returns (uint256) { let r: uint256 = x; r -= y; return r; }",
  "function mulAssign256u(x: uint256, y: uint256) returns (uint256) { let r: uint256 = x; r *= y; return r; }",
  "function addAssign8s(x: int8, y: int8) returns (int8) { let r: int8 = x; r += y; return r; }",
  "function subAssign8s(x: int8, y: int8) returns (int8) { let r: int8 = x; r -= y; return r; }",
  "function mulAssign8s(x: int8, y: int8) returns (int8) { let r: int8 = x; r *= y; return r; }",
  "function addAssign256s(x: int256, y: int256) returns (int256) { let r: int256 = x; r += y; return r; }",
  "function subAssign256s(x: int256, y: int256) returns (int256) { let r: int256 = x; r -= y; return r; }",
  "function mulAssign256s(x: int256, y: int256) returns (int256) { let r: int256 = x; r *= y; return r; }",
  "function andAssign8u(x: uint8, y: uint8) returns (uint8) { let r: uint8 = x; r &= y; return r; }",
  "function orAssign8s(x: int8, y: int8) returns (int8) { let r: int8 = x; r |= y; return r; }",
  "function xorAssign16u(x: uint16, y: uint16) returns (uint16) { let r: uint16 = x; r ^= y; return r; }",
  "function tableAdd8u(x: uint8, y: uint8) returns (uint8) { let table: mapping(Word => uint8); table[7] = x; table[7] += y; return table[7]; }",
  "function absentAdd8u(y: uint8) returns (uint8) { let r: uint8; r += y; return r; }",
  "function div8u(x: uint8, y: uint8) returns (uint8) { return x / y; }",
  "function mod8u(x: uint8, y: uint8) returns (uint8) { return x % y; }",
  "function div256u(x: uint256, y: uint256) returns (uint256) { return x / y; }",
  "function mod256u(x: uint256, y: uint256) returns (uint256) { return x % y; }",
  "function div8s(x: int8, y: int8) returns (int8) { return x / y; }",
  "function mod8s(x: int8, y: int8) returns (int8) { return x % y; }",
  "function div256s(x: int256, y: int256) returns (int256) { return x / y; }",
  "function mod256s(x: int256, y: int256) returns (int256) { return x % y; }",
  "function divAssign8u(x: uint8, y: uint8) returns (uint8) { let r: uint8 = x; r /= y; return r; }",
  "function modAssign8u(x: uint8, y: uint8) returns (uint8) { let r: uint8 = x; r %= y; return r; }",
  "function divAssign8s(x: int8, y: int8) returns (int8) { let r: int8 = x; r /= y; return r; }",
  "function modAssign8s(x: int8, y: int8) returns (int8) { let r: int8 = x; r %= y; return r; }",
  "function divAssign256s(x: int256, y: int256) returns (int256) { let r: int256 = x; r /= y; return r; }",
  "function modAssign256u(x: uint256, y: uint256) returns (uint256) { let r: uint256 = x; r %= y; return r; }",
  "function tableDiv8s(x: int8, y: int8) returns (int8) { let table: mapping(Word => int8); table[7] = x; table[7] /= y; return table[7]; }",
  "function lit8u() returns (uint8) { return 255; }",
  "function lit256u() returns (uint256) { return 115792089237316195423570985008687907853269984665640564039457584007913129639935; }",
  "function lit8s() returns (int8) { return 127; }",
  "function lit256s() returns (int256) { return 57896044618658097711785492504343953926634992332820282019728792003956564819967; }",
  "function zero8s() returns (int8) { return 0; }",
  "function inc8u(x: uint8) returns (uint8) { return x + 1; }",
  "function inc256s(x: int256) returns (int256) { return x + 1; }",
  "function below8s(x: int8) returns (bool) { return x < 100; }",
  "function isZero256u(x: uint256) returns (bool) { return x == 0; }",
  "function doubleAssign8u(x: uint8) returns (uint8) { let r: uint8 = x; r *= 2; return r; }",
  "function half8s(x: int8) returns (int8) { return x / 2; }",
  "function tenthAssign256u(x: uint256) returns (uint256) { let r: uint256 = x; r %= 10; return r; }",
  "function deferredDiv8u() returns (uint8) { let a = 6 / 2; let b: uint8 = a; return b; }",
  "function deferredMod8s() returns (int8) { let a = 7 % 4; let b: int8 = a; return b; }",
  "function tableLit8u() returns (uint8) { let table: mapping(uint8 => uint8); table[3] = 200; return table[3]; }",
  "function tableLit8s(k: Word) returns (int8) { let table: mapping(Word => int8); table[k] = 127; return table[k]; }",
  "function mask16u(x: uint16) returns (uint16) { return x & 255; }",
  "function deferredAdd8u() returns (uint8) { let a = 200 + 100; let b: uint8 = a; return b; }",
  "function negLit8s() returns (int8) { return -128; }",
  "function negGroup8s() returns (int8) { return (-128); }",
  "function negOfGroup8s() returns (int8) { return -(128); }",
  "function doubleNeg8s() returns (int8) { return - -5; }",
  "function negLit256s() returns (int256) { return -57896044618658097711785492504343953926634992332820282019728792003956564819968; }",
  "function negZero8u() returns (uint8) { return -0; }",
  "function negOneWord() returns (Word) { let w: Word = -1; return w; }",
  "function letNegative() returns (Word) { let k = -1; return k; }",
  "function neg8s(x: int8) returns (int8) { return -x; }",
  "function neg8u(x: uint8) returns (uint8) { return -x; }",
  "function neg256s(x: int256) returns (int256) { return -x; }",
  "function neg256u(x: uint256) returns (uint256) { return -x; }",
  "function negWord(w: Word) returns (Word) { return -w; }",
  "function addNegLit8s(x: int8) returns (int8) { return x + -1; }",
  "function mulNegLit256s(x: int256) returns (int256) { return x * -2; }",
  "function compoundNeg8s(x: int8) returns (int8) { let r: int8 = x; r += -5; return r; }",
  "function compoundNeg256s(x: int256) returns (int256) { let r: int256 = x; r -= -1; return r; }",
  "function nestedNeg8s(x: int8) returns (int8) { return - -x; }",
  "function nestedNegGroup8s(x: int8) returns (int8) { return -(-x); }",
  "function blockNegWord(w: Word) returns (Word) { unchecked { let r: Word = -w; return r; } }",
  "function belowNegLit8s(x: int8) returns (bool) { return x < -100; }",
  "function tableNeg8s() returns (int8) { let table: mapping(Word => int8); table[1] = -128; return table[1]; }"
]

private def names : List String :=
  ["eq8", "ne16", "lt32", "le64", "gt128", "ge256", "and8", "or16", "xor32", "eqSigned", "mixed",
    "and8s", "or16s", "xor256s", "not8s", "not256s", "not256u", "lt8s", "ge16s", "gt256s", "le32s",
    "not8u", "not16u", "not128u", "add8u", "sub16u", "mul32u", "add256u", "mul256u", "add8s", "sub8s",
    "mul8s", "sub256s", "mul256s", "addAssign8u", "subAssign8u", "mulAssign8u", "addAssign256u",
    "subAssign256u", "mulAssign256u", "addAssign8s", "subAssign8s", "mulAssign8s", "addAssign256s",
    "subAssign256s", "mulAssign256s", "andAssign8u", "orAssign8s", "xorAssign16u", "tableAdd8u", "absentAdd8u",
    "div8u", "mod8u", "div256u", "mod256u", "div8s", "mod8s", "div256s", "mod256s", "divAssign8u",
    "modAssign8u", "divAssign8s", "modAssign8s", "divAssign256s", "modAssign256u", "tableDiv8s", "lit8u",
    "lit256u", "lit8s", "lit256s", "zero8s", "inc8u", "inc256s", "below8s", "isZero256u", "doubleAssign8u",
    "half8s", "tenthAssign256u", "deferredDiv8u", "deferredMod8s", "tableLit8u", "tableLit8s", "mask16u",
    "deferredAdd8u", "negLit8s", "negGroup8s", "negOfGroup8s", "doubleNeg8s", "negLit256s", "negZero8u",
    "negOneWord", "letNegative", "neg8s", "neg8u", "neg256s", "neg256u", "negWord",
    "addNegLit8s", "mulNegLit256s", "compoundNeg8s", "compoundNeg256s", "nestedNeg8s", "nestedNegGroup8s", "blockNegWord", "belowNegLit8s", "tableNeg8s"]

private def seed (program : CheckedProgram) (name : String) : IO Seed :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure (SourceCoreCompiler.Seed.declaration signature.id)
  | _ => throw (IO.userError s!"fixed-width operator fixture missing {name}")
private def execute {artifact : Artifact} (session : Session artifact) (key : Key) (arguments : List Value) :
    IO (Completion artifact) := do
  let executed ← session.runWithReceipt key arguments {executionFuel := 300000}
  match executed.val with
  | .ok (.succeeded result) => pure result
  | .ok (.exportError error _) => throw (IO.userError s!"fixed-width operator export: {reprStr error}")
  | .ok (.failed reason _) => throw (IO.userError s!"fixed-width operator failure: {reprStr reason}")
  | .ok (.outOfFuel _) => throw (IO.userError "fixed-width operator execution exhausted")
  | .error error => throw (IO.userError s!"fixed-width operator invocation: {reprStr error}")
/-- A run that fails with `Panic(code)`: the reason is the panic's, the
diagnostic decodes it, and the revert data is upstream's. -/
private def panics {artifact : Artifact} (session : Session artifact) (key : Key) (arguments : List Value)
    (code : UInt8) (label : String) : IO (Session artifact) := do
  let executed ← session.runWithReceipt key arguments {executionFuel := 300000}
  match executed.val with
  | .ok (.failed reason next) =>
      require (SourceCorePanics.code? reason == some code) s!"{label} failed with {reprStr reason}"
      match session.diagnostic key reason with
      | .ok (some diagnostic) =>
          require (decide (diagnostic.error = .panic code)) s!"{label} decoded {reprStr diagnostic.error}"
      | other => throw (IO.userError s!"{label} decoded {reprStr other}")
      let data := ((SourceCorePanics.code? reason).map SourceCorePanics.revertData).map ByteArray.toList
      require (data == some ([0x4e, 0x48, 0x7b, 0x71] ++ List.replicate 31 0 ++ [code]))
        s!"{label} revert data {reprStr data}"
      pure next
  | .ok (.succeeded result) => throw (IO.userError s!"{label} gave {reprStr result.value}")
  | .ok _ => throw (IO.userError s!"{label} did not fail")
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
/-- A run that fails on an absent compound-assignment operand: the reason is
the assignment's own diagnostic site, which names the operator and the target's
type. -/
private def invalidOperands {artifact : Artifact} (session : Session artifact) (key : Key) (arguments : List Value)
    (expected : SourceTypedRuntime.RuntimeError) (label : String) : IO (Session artifact) := do
  let executed ← session.runWithReceipt key arguments {executionFuel := 300000}
  match executed.val with
  | .ok (.failed reason next) =>
      require (reason != Core.Word.zero) s!"{label} failed with reason zero"
      match session.diagnostic key reason with
      | .ok (some diagnostic) =>
          require (decide (diagnostic.error = expected)) s!"{label} decoded {reprStr diagnostic.error}"
      | other => throw (IO.userError s!"{label} decoded {reprStr other}")
      pure next
  | .ok (.succeeded result) => throw (IO.userError s!"{label} gave {reprStr result.value}")
  | .ok _ => throw (IO.userError s!"{label} did not fail")
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def boot (artifact : Artifact) : IO (Session artifact) := do
  let fresh ← artifact.bootstrapWithReceipt
  match fresh.val.resume 300000 with
  | .ready session => pure session
  | .error error => throw (IO.userError s!"fixed-width operator bootstrap: {reprStr error}")
  | .outOfFuel _ => throw (IO.userError "fixed-width operator bootstrap exhausted")

/-- Inference itself rejects the program, after loading succeeded. -/
private def rejectedByInference (label : String) (lines : List String) : IO Unit :=
  match checkProgram (workspaceOf lines) with
  | .ok _ => throw (IO.userError s!"{label} was accepted")
  | .error [.inference _] => pure ()
  | .error errors => throw (IO.userError s!"{label} gave {reprStr errors}")

/-- Inference rejects a literal above its fixed-width type's greatest value,
and the diagnostic names the type and the literal's value. -/
private def rejectedOutOfRange (label : String) (name : String) (value : Int) (lines : List String) :
    IO Unit := do
  let type ← match TypeSystem.FixedInteger.ofName? name with
    | some type => pure type | none => throw (IO.userError s!"{name} missing")
  match checkProgram (workspaceOf lines) with
  | .error [.inference ⟨_, .integerLiteralOutOfRange _ actual actualValue⟩] =>
      require (decide (actual = TypeSystem.Ty.fixed type) && actualValue == value)
        s!"{label} named {reprStr actual} and {actualValue}"
  | .ok _ => throw (IO.userError s!"{label} was accepted")
  | .error errors => throw (IO.userError s!"{label} gave {reprStr errors}")

/-- Step 7's fixture: an open literal defaults to `uint256` in an operator, a
comparison, a requirement or a match, and numeric patterns are admitted at
`uint256`. -/
private def defaultingWorkspace : Workspace.RawWorkspace := workspaceOf [
  "function sc_id<A>(x: A) returns (A) { return x; }",
  "trait Mark<T> {}",
  "impl Mark<uint256> {}",
  "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
  "function eqOpen() returns (bool) { return 7 == 7; }",
  "function addUnused() returns (Word) { let a = 7 + 1; return 3; }",
  "function idOpen() returns (Word) { return sc_id(7); }",
  "function shiftUnused() returns (Word) { let s = 1 << 3; return 5; }",
  "function shiftOpen() returns (bool) { return (1 << 3) == 8; }",
  "function matchOpen() returns (Word) { match (7) { case 7 { return 1; } default { return 0; } } }",
  "function matchOpenMiss() returns (Word) { match (8) { case 7 { return 1; } default { return 0; } } }",
  "function matchU256(x: uint256) returns (Word) { match (x) { case 0 { return 10; } case 0xff { return 20; } case 115792089237316195423570985008687907853269984665640564039457584007913129639935 { return 30; } default { return 40; } } }",
  "function maxOpen() returns (bool) { return 115792089237316195423570985008687907853269984665640564039457584007913129639935 == 115792089237316195423570985008687907853269984665640564039457584007913129639935; }",
  "function addOpen() returns (bool) { return 7 + 1 == 8; }",
  "function overflowOpen() returns (bool) { return 115792089237316195423570985008687907853269984665640564039457584007913129639935 + 1 == 0; }",
  "function underflowOpen() returns (bool) { return 0 - 1 == 0; }",
  "function markOpen() returns (Word) { keep(7); return 4; }",
  "function compoundOpen() returns (bool) { let x = 0; x -= 1; return x > 5; }",
  "function rewrittenOpen() returns (bool) { let x = 0; x = x - 1; return x > 5; }",
  "function compoundWord(w: Word) returns (Word) { let total = 0; total += w; return total; }",
  "function compoundAddOpen() returns (bool) { let x = 0; x += 7; return x == 7; }",
  "function compoundAddMax() returns (bool) { let x = 115792089237316195423570985008687907853269984665640564039457584007913129639935; x += 1; return x == 0; }",
  "function compoundMulOpen() returns (bool) { let x = 57896044618658097711785492504343953926634992332820282019728792003956564819968; x *= 2; return x == 0; }",
  "function compoundDivZero() returns (bool) { let x = 1; x /= 0; return x == 0; }",
  "function compoundModZero() returns (bool) { let x = 1; x %= 0; return x == 0; }",
  "function compoundBitsOpen() returns (bool) { let x = 12; x &= 10; let y = 12; y |= 3; let z = 12; z ^= 10; return x + y + z == 29; }",
  "function deferredCompound8u() returns (uint8) { let x = 200; x += 55; return x; }",
  "function deferredCompound8uOver() returns (uint8) { let x = 200; x += 56; return x; }",
  "function deferredCompound8s() returns (int8) { let x = -100; x -= 28; return x; }",
  "function deferredCompound8sUnder() returns (int8) { let x = -100; x -= 29; return x; }",
  "function loopOpen() returns (uint256) { let total = 0; for (let i = 0; i < 4; i += 1) { total += i; } return total; }",
  "function loopWord(n: Word) returns (Word) { let total = 0; for (let i = 0; i < n; i += 1) { total += 1; } return total; }",
  "function shiftCompoundOpen() returns (bool) { let x = 1; x <<= 3; return x == 8; }",
  "function uncheckedCompoundOpen() returns (bool) { let x = 0; unchecked { x -= 1; } return x > 5; }",
  "function lambdaCaptured(w: Word) returns (Word) { let f = lam(acc) { acc += w; return acc; }; return f(5); }",
  "function lambdaAnnotated() returns (Word) { let f = lam(acc: Word) { acc += 1; return acc; }; return f(41); }",
  "function lambdaLiteral() returns (uint256) { let f = lam(acc) { acc += 1; return acc; }; return f(41); }"]

private def defaultingNames : List String := [
  "eqOpen", "addUnused", "idOpen", "shiftUnused", "shiftOpen", "matchOpen", "matchOpenMiss",
  "matchU256", "maxOpen", "addOpen", "overflowOpen", "underflowOpen", "markOpen",
  "compoundOpen", "rewrittenOpen", "compoundWord",
  "compoundAddOpen", "compoundAddMax", "compoundMulOpen", "compoundDivZero", "compoundModZero", "compoundBitsOpen",
  "deferredCompound8u", "deferredCompound8uOver", "deferredCompound8s", "deferredCompound8sUnder", "loopOpen", "loopWord", "shiftCompoundOpen", "uncheckedCompoundOpen",
  "lambdaCaptured", "lambdaAnnotated", "lambdaLiteral"]

/-- Inference rejects an open literal that nothing constrains, naming it. -/
private def rejectedAmbiguous (label : String) (lines : List String) : IO Unit :=
  match checkProgram (workspaceOf lines) with
  | .error [.inference ⟨_, .ambiguousIntegerLiteral _⟩] => pure ()
  | .ok _ => throw (IO.userError s!"{label} was accepted")
  | .error errors => throw (IO.userError s!"{label} gave {reprStr errors}")

/-- Inference rejects a numeric pattern above `uint256`'s greatest value at
`uint256`, declared or defaulted, and names the type and the value. -/
private def rejectedPatternOutOfRange (label : String) (value : Nat) (lines : List String) : IO Unit :=
  match checkProgram (workspaceOf lines) with
  | .error [.inference ⟨_, .integerPatternOutOfRange _ type actual⟩] =>
      require (decide (type = TypeSystem.Ty.fixed .uint256) && actual == value)
        s!"{label} named {reprStr type} and {actual}"
  | .ok _ => throw (IO.userError s!"{label} was accepted")
  | .error errors => throw (IO.userError s!"{label} gave {reprStr errors}")

/-- Step 7, the `uint256` default, through the public API. -/
def runDefaulting : IO Unit := do
  let program ← get "uint256 default check" (checkProgram defaultingWorkspace)
  let seeds ← defaultingNames.mapM (seed program)
  let compiled ← get "uint256 default compilation"
    (compile defaultingWorkspace seeds {specializationBudget := 256, compilationFuel := 1000})
  let key (index : Nat) : IO Key := match compiled.keys[index]? with
    | some key => pure key | none => throw (IO.userError "uint256 default root missing")
  let mut session ← boot (← compiled.open)
  let cases : List (Nat × List Value × Value) := [
    -- Two open literals compared, or added and unused, are `uint256`.
    (0, [], boolean true), (1, [], word 3),
    -- A literal through a generic call takes the return's type; a shift's open literals default to
    -- `uint256` too.
    (2, [], word 7), (3, [], word 5), (4, [], boolean true),
    -- A match on an open literal makes it and its pattern `uint256`.
    (5, [], word 1), (6, [], word 0),
    -- Numeric patterns at `uint256`, up to its greatest value.
    (7, [word 0], word 10), (7, [word 0xff], word 20), (7, [word (modulus - 1)], word 30),
    (7, [word 7], word 40), (7, [word 256], word 40),
    -- `2^256 - 1` defaulted, and checked addition on defaulted literals.
    (8, [], boolean true), (9, [], boolean true),
    -- A literal in a pending `Mark` requirement is `uint256`, and `impl Mark<uint256>` solves it.
    (12, [], word 4),
    -- A `word` operand types the open target `word`, here and upstream.
    (15, [word 9], word 9),
    -- Step 7b: a compound assignment on an open target takes its operand's type and counts as an
    -- operator use, as upstream's rewrite to `x = x op e` types it, so the target is `uint256`.
    (16, [], boolean true), (21, [], boolean true),
    -- A later use gives the open target its type: `uint8` and `int8` at their range edges.
    (22, [], word 255), (24, [], word (modulus - 128)),
    -- A `for` loop's post `i += 1`: `uint256` counters, or `Word` ones under a `Word` bound.
    (26, [], word 6), (27, [word 3], word 3),
    -- Since step 8d a compound shift's open target and amount default to `uint256`. Since step 8b
    -- an unchecked compound on an open target takes its operand's type, here `uint256`, which wraps
    -- as Word does.
    (28, [], boolean true), (29, [], boolean true),
    -- A lambda parameter as a compound target: typed by a captured `Word` in the body, declared
    -- `Word`, or tied to its literal operand, which keeps it monomorphic, so the call types it.
    (30, [word 2], word 7), (31, [], word 42), (32, [], word 42)]
  for (index, arguments, expected) in cases do
    let completed ← execute session (← key index) arguments
    require (completed.value == expected)
      s!"{defaultingNames[index]?} on {reprStr arguments} gave {reprStr completed.value}"
    session := completed.session
  -- Arithmetic on defaulted literals is checked: past `uint256`'s range it panics with 0x11,
  -- `x = x - 1` on an open `x` too, and since step 7b `x -= 1`, `x += 1` and `x *= 2` on one.
  for index in [10, 11, 13, 14, 17, 18, 23, 25] do
    session ← panics session (← key index) [] SourceCorePanics.arithmetic s!"{defaultingNames[index]?}"
  -- A zero divisor in `x /= 0` and `x %= 0` on an open target panics with 0x12.
  for index in [19, 20] do
    session ← panics session (← key index) [] SourceCorePanics.divisionByZero s!"{defaultingNames[index]?}"
  -- An open literal that nothing constrains is ambiguous; it never defaults to Word.
  rejectedAmbiguous "an unused let y = 7" ["function bad() returns (Word) { let y = 7; return 0; }"]
  rejectedAmbiguous "let y = 7; let z = y" ["function bad() returns (Word) { let y = 7; let z = y; return 0; }"]
  rejectedAmbiguous "sc_id(7) with an unused result"
    ["function sc_id<A>(x: A) returns (A) { return x; }", "function bad() returns (Word) { sc_id(7); return 0; }"]
  rejectedAmbiguous "a lambda returning 7, never called"
    ["function bad() returns (Word) { let f = lam () { return 7; }; return 0; }"]
  -- An open negative literal defaults to `uint256` and is out of its range, as upstream's SC0411.
  rejectedOutOfRange "an open let k = -1" "uint256" (-1) ["function bad() returns (Word) { let k = -1; return 0; }"]
  rejectedOutOfRange "2^256 defaulted" "uint256" 115792089237316195423570985008687907853269984665640564039457584007913129639936
    ["function bad() returns (bool) { return 115792089237316195423570985008687907853269984665640564039457584007913129639936 == 0; }"]
  -- The requirement a literal defaults for must be solved at `uint256`: here no implementation does.
  match checkProgram (workspaceOf ["trait Mark<T> {}", "impl Mark<Word> {}",
      "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
      "function bad() returns (Word) { keep(7); return 0; }"]) with
  | .error [.noSolution _ predicate] =>
      require (decide (predicate.subject = TypeSystem.Ty.fixed .uint256))
        s!"the unsolved Mark requirement named {reprStr predicate.subject}"
  | .ok _ => throw (IO.userError "a Mark requirement without impl Mark<uint256> was accepted")
  | .error errors => throw (IO.userError s!"a Mark requirement without impl Mark<uint256> gave {reprStr errors}")
  -- Numeric patterns stay rejected on the other eleven types.
  for name in ["uint8", "uint16", "uint32", "uint64", "uint128", "int8", "int16", "int32", "int64", "int128", "int256"] do
    rejectedByInference s!"a numeric pattern on {name}"
      [s!"function bad(x: {name}) returns (Word) \{ match (x) \{ case 1 \{ return 1; } default \{ return 0; } } }"]
  -- A numeric pattern is range-checked at `uint256`, declared or defaulted, as upstream's
  -- `check_integer_literal_pattern_range` does.
  rejectedPatternOutOfRange "a numeric pattern of 2^256 at uint256" 115792089237316195423570985008687907853269984665640564039457584007913129639936
    ["function bad(x: uint256) returns (Word) { match (x) { case 115792089237316195423570985008687907853269984665640564039457584007913129639936 { return 1; } default { return 0; } } }"]
  rejectedPatternOutOfRange "a defaulted numeric pattern of 2^256" 115792089237316195423570985008687907853269984665640564039457584007913129639936
    ["function bad() returns (Word) { match (7) { case 115792089237316195423570985008687907853269984665640564039457584007913129639936 { return 1; } default { return 0; } } }"]
  -- Upstream's `crates/uitest/tests/fixtures/solver/poly_int_defaulting`, verbatim, its leading
  -- `pragma solcore;` added by `workspaceOf`. Upstream rejects it in inference as ambiguous (SC0299);
  -- Lean rejects it earlier, at the signature, because a `where` clause cannot name the builtin `Int`.
  match checkProgram (workspaceOf ["",
      "function poly<a>(x: a) returns (a) where a: Int {", "    return x;", "}", "",
      "function f() returns (word) {", "    let y = poly(7);", "    return 0;", "}"]) with
  | .error [.signature (.unknownTrait _ name)] =>
      require (name == "Int") s!"poly_int_defaulting named the unknown trait {name}"
  | .ok _ => throw (IO.userError "poly_int_defaulting was accepted")
  | .error errors => throw (IO.userError s!"poly_int_defaulting gave {reprStr errors}")
  -- Without the bound upstream's rules give SC0299 too: no non-`Int` obligation constrains the
  -- literal, and `f`'s root type holds no variable.
  rejectedAmbiguous "an unbounded poly(7) with an unused result"
    ["function poly<a>(x: a) returns (a) { return x; }", "function f() returns (word) { let y = poly(7); return 0; }"]
  -- Step 7b: finalization checks the open compound target's type: one that becomes `integer`
  -- takes no compound operator.
  match checkProgram (workspaceOf
      ["function bad() returns (Word) { let x = 0; x += 1; let y: integer = x; return 0; }"]) with
  | .error [.inference ⟨_, .compoundTargetNotSupported _ operator type⟩] =>
      require (operator == .add && decide (type = TypeSystem.Ty.integer))
        s!"an integer compound target named {reprStr operator} and {reprStr type}"
  | .ok _ => throw (IO.userError "an integer compound target was accepted")
  | .error errors => throw (IO.userError s!"an integer compound target gave {reprStr errors}")
  -- A compound on a lambda parameter that nothing else types: local generalization quantifies
  -- the parameter, so its type is still open at finalization, as `acc + step` was rejected
  -- before. Upstream keeps closures monomorphic.
  match checkProgram (workspaceOf
      ["function bad() returns (Word) { let f = lam(acc, step) { acc += step; return acc; }; return 0; }"]) with
  | .error [.inference ⟨_, .compoundTargetNotSupported _ operator (.variable _)⟩] =>
      require (operator == .add) s!"a generalized lambda's compound target named {reprStr operator}"
  | .ok _ => throw (IO.userError "a compound on a generalized lambda parameter was accepted")
  | .error errors => throw (IO.userError s!"a compound on a generalized lambda parameter gave {reprStr errors}")
  -- So are an in-place `~` (step 9a) and a compound shift (step 8d) on such a parameter.
  match checkProgram (workspaceOf
      ["function bad() returns (Word) { let f = lam(x) { x ~=; return x; }; return 0; }"]) with
  | .error [.inference ⟨_, .operatorNotSupported name (.variable _)⟩] =>
      require (name == "BitNot") s!"a generalized lambda's in-place ~ named {name}"
  | .ok _ => throw (IO.userError "an in-place ~ on a generalized lambda parameter was accepted")
  | .error errors => throw (IO.userError s!"an in-place ~ on a generalized lambda parameter gave {reprStr errors}")
  match checkProgram (workspaceOf
      ["function bad() returns (Word) { let f = lam(x) { x <<= 1; return x; }; return 0; }"]) with
  | .error [.inference ⟨_, .compoundTargetNotSupported _ operator (.variable _)⟩] =>
      require (operator == .shiftLeft) s!"a generalized lambda's compound shift named {reprStr operator}"
  | .ok _ => throw (IO.userError "a compound shift on a generalized lambda parameter was accepted")
  | .error errors => throw (IO.userError s!"a compound shift on a generalized lambda parameter gave {reprStr errors}")
  IO.println "SOURCE_CORE_UINT256_DEFAULT_PASS: open literals in comparisons, operators, requirements and matches default to uint256 with checked arithmetic, a generic call's literal takes the return's type, a shift's open literals defaulted to uint256, numeric patterns at uint256 up to 2^256 - 1, unconstrained literals rejected as ambiguous, an open -1 and a defaulted 2^256 out of uint256's range, an unsolved Mark<uint256> rejected, compound assignments on an open target typed with their operand and defaulted to uint256 with checked += -= *= /= %= and Word's &= |= ^=, a later use's uint8 and int8, uint256 and Word for loop counters, compound shifts still Word and an open unchecked compound uint256, an integer compound target rejected, lambda parameters as compound targets typed by a captured Word, a declaration or a literal operand, and one that nothing types rejected, as are an in-place ~ and a compound shift on one, numeric patterns on the other eleven types rejected, a 2^256 pattern at uint256 rejected by inference, declared or defaulted, upstream's poly_int_defaulting rejected at its Int bound and its unbounded form as ambiguous"

/-- Step 8a's fixture: unchecked `+ - * / %` on the twelve types, in a block. -/
private def uncheckedWorkspace : Workspace.RawWorkspace := workspaceOf [
  "function uadd8u(x: uint8, y: uint8) returns (uint8) { unchecked { return x + y; } }",
  "function usub8u(x: uint8, y: uint8) returns (uint8) { unchecked { return x - y; } }",
  "function umul16u(x: uint16, y: uint16) returns (uint16) { unchecked { return x * y; } }",
  "function uadd256u(x: uint256, y: uint256) returns (uint256) { unchecked { return x + y; } }",
  "function usub256u(x: uint256, y: uint256) returns (uint256) { unchecked { return x - y; } }",
  "function uadd8s(x: int8, y: int8) returns (int8) { unchecked { return x + y; } }",
  "function usub8s(x: int8, y: int8) returns (int8) { unchecked { return x - y; } }",
  "function umul8s(x: int8, y: int8) returns (int8) { unchecked { return x * y; } }",
  "function umul256s(x: int256, y: int256) returns (int256) { unchecked { return x * y; } }",
  "function uadd64s(x: int64, y: int64) returns (int64) { unchecked { return x + y; } }",
  "function udiv8u(x: uint8, y: uint8) returns (uint8) { unchecked { return x / y; } }",
  "function umod8u(x: uint8, y: uint8) returns (uint8) { unchecked { return x % y; } }",
  "function udiv8s(x: int8, y: int8) returns (int8) { unchecked { return x / y; } }",
  "function umod8s(x: int8, y: int8) returns (int8) { unchecked { return x % y; } }",
  "function udiv256s(x: int256, y: int256) returns (int256) { unchecked { return x / y; } }",
  "function umod256u(x: uint256, y: uint256) returns (uint256) { unchecked { return x % y; } }",
  "function uneg8s(x: int8) returns (int8) { unchecked { return -x; } }",
  "function uneg8u(x: uint8) returns (uint8) { unchecked { return -x; } }",
  "function uneg256u(x: uint256) returns (uint256) { unchecked { return -x; } }",
  "function uinc8u(x: uint8) returns (uint8) { unchecked { return x + 1; } }",
  "function ulitLeft8s(x: int8) returns (int8) { unchecked { return 100 - x; } }",
  "function uletTyped16u(x: uint16) returns (uint16) { unchecked { let r: uint16 = x * 2; return r; } }",
  "function uassign8u(x: uint8, y: uint8) returns (uint8) { let s: uint8 = 0; unchecked { s = x + y; } return s; }",
  "function ucompare8s(x: int8) returns (bool) { unchecked { return x + 1 < x; } }",
  "function uscope8u(x: uint8) returns (uint8) { unchecked { let a: uint8 = x + 1; } return x + 1; }",
  "function uaddAssign8u(x: uint8, y: uint8) returns (uint8) { let r: uint8 = x; unchecked { r += y; } return r; }",
  "function usubAssign8u(x: uint8, y: uint8) returns (uint8) { let r: uint8 = x; unchecked { r -= y; } return r; }",
  "function umulAssign8s(x: int8, y: int8) returns (int8) { let r: int8 = x; unchecked { r *= y; } return r; }",
  "function udivAssign8s(x: int8, y: int8) returns (int8) { let r: int8 = x; unchecked { r /= y; } return r; }",
  "function umodAssign8s(x: int8, y: int8) returns (int8) { let r: int8 = x; unchecked { r %= y; } return r; }",
  "function udivAssign8u(x: uint8, y: uint8) returns (uint8) { let r: uint8 = x; unchecked { r /= y; } return r; }",
  "function uaddAssign256s(x: int256, y: int256) returns (int256) { let r: int256 = x; unchecked { r += y; } return r; }",
  "function usubAssign256u(x: uint256, y: uint256) returns (uint256) { let r: uint256 = x; unchecked { r -= y; } return r; }",
  "function udivAssign256s(x: int256, y: int256) returns (int256) { let r: int256 = x; unchecked { r /= y; } return r; }",
  "function utableAdd16s(x: int16, y: int16) returns (int16) { let table: mapping(Word => int16); table[3] = x; unchecked { table[3] += y; } return table[3]; }",
  "function uopenAssign8u() returns (uint8) { let x = 200; unchecked { x += 100; } return x; }",
  "function uabsentAdd8u(y: uint8) returns (uint8) { let r: uint8; unchecked { r += y; } return r; }",
  "function uopenLits8u() returns (uint8) { unchecked { let a = 200 + 100; let b: uint8 = a; return b; } }",
  "function uopenReturn256() returns (uint256) { unchecked { return 1 + 2; } }",
  "function uopenUnused() returns (Word) { unchecked { let a = 1 + 2; } return 0; }",
  "function uopenDefaultCompare() returns (bool) { unchecked { let a = 0 - 1; return a > 5; } }",
  "function uopenWord() returns (Word) { unchecked { let a = 0 - 1; let b: Word = a; return b; } }"]

private def uncheckedNames : List String := [
  "uadd8u", "usub8u", "umul16u", "uadd256u", "usub256u", "uadd8s", "usub8s", "umul8s", "umul256s", "uadd64s",
  "udiv8u", "umod8u", "udiv8s", "umod8s", "udiv256s", "umod256u", "uneg8s", "uneg8u", "uneg256u", "uinc8u",
  "ulitLeft8s", "uletTyped16u", "uassign8u", "ucompare8s", "uscope8u", "uaddAssign8u", "usubAssign8u",
  "umulAssign8s", "udivAssign8s", "umodAssign8s", "udivAssign8u", "uaddAssign256s", "usubAssign256u",
  "udivAssign256s", "utableAdd16s", "uopenAssign8u", "uabsentAdd8u", "uopenLits8u", "uopenReturn256",
  "uopenUnused", "uopenDefaultCompare", "uopenWord"]

/-- Step 8a, unchecked `+ - * / %` on the twelve types, through the public API:
the exact result wrapped to the type's width, `MIN / -1` giving `MIN`, and
`Panic(0x12)` on a zero divisor, as upstream's `UncheckedAdd` … `UncheckedMod`
instances give. -/
def runUnchecked : IO Unit := do
  let program ← get "unchecked fixed-width check" (checkProgram uncheckedWorkspace)
  let seeds ← uncheckedNames.mapM (seed program)
  let compiled ← get "unchecked fixed-width compilation"
    (compile uncheckedWorkspace seeds {specializationBudget := 256, compilationFuel := 1000})
  let key (index : Nat) : IO Key := match compiled.keys[index]? with
    | some key => pure key | none => throw (IO.userError "unchecked fixed-width root missing")
  let mut session ← boot (← compiled.open)
  let cases : List (Nat × List Value × Value) := [
    -- `+ - *` wrap modulo `2^N` on the unsigned types.
    (0, [word 200, word 100], word 44), (0, [word 255, word 1], word 0), (0, [word 3, word 4], word 7),
    (1, [word 3, word 5], word 254), (1, [word 5, word 3], word 2),
    (2, [word 256, word 256], word 0), (2, [word 300, word 300], word 24464),
    (3, [word (modulus - 1), word 1], word 0), (3, [word (2 ^ 255), word (2 ^ 255)], word 0),
    (4, [word 0, word 1], word (modulus - 1)),
    -- On the signed types they wrap in two's complement, and the result stays sign-extended.
    (5, [word 127, word 1], word (modulus - 128)), (5, [word (modulus - 128), word (modulus - 1)], word 127),
    (6, [word (modulus - 128), word 1], word 127), (6, [word 0, word (modulus - 128)], word (modulus - 128)),
    (7, [word (modulus - 128), word (modulus - 1)], word (modulus - 128)), (7, [word 64, word 2], word (modulus - 128)),
    (7, [word 16, word 16], word 0), (7, [word (modulus - 3), word 5], word (modulus - 15)),
    (8, [word (2 ^ 255), word (modulus - 1)], word (2 ^ 255)), (8, [word (2 ^ 254), word 2], word (2 ^ 255)),
    (9, [word (2 ^ 63 - 1), word 1], word (modulus - 2 ^ 63)),
    -- `/ %` round toward zero; `MIN / -1` wraps to `MIN`, and `MIN % -1` is 0.
    (10, [word 7, word 2], word 3), (10, [word 255, word 255], word 1), (11, [word 7, word 2], word 1),
    (12, [word (modulus - 128), word (modulus - 1)], word (modulus - 128)),
    (12, [word (modulus - 7), word 2], word (modulus - 3)), (12, [word 7, word (modulus - 2)], word (modulus - 3)),
    (13, [word (modulus - 7), word 2], word (modulus - 1)), (13, [word (modulus - 128), word (modulus - 1)], word 0),
    (13, [word 7, word (modulus - 2)], word 1),
    (14, [word (2 ^ 255), word (modulus - 1)], word (2 ^ 255)), (14, [word (modulus - 6), word 3], word (modulus - 2)),
    (15, [word (modulus - 1), word 10], word 5),
    -- `-x` in a block is unchecked `0 - x`: `-MIN` is `MIN`, and on an unsigned type it is `2^N - x`.
    (16, [word (modulus - 128)], word (modulus - 128)), (16, [word 5], word (modulus - 5)), (16, [word 0], word 0),
    (17, [word 1], word 255), (17, [word 0], word 0), (17, [word 255], word 1),
    (18, [word 1], word (modulus - 1)),
    -- A literal operand takes the other operand's type, on either side.
    (19, [word 255], word 0), (19, [word 7], word 8),
    (20, [word (modulus - 100)], word (modulus - 56)), (20, [word 5], word 95),
    (21, [word 40000], word 14464), (22, [word 200, word 100], word 44),
    (23, [word 127], boolean true), (23, [word 0], boolean false),
    -- Arithmetic after the block is checked again.
    (24, [word 7], word 8),
    -- Step 8b: `+= -= *= /= %=` in a block on a fixed-width target wrap as the binary forms do.
    (25, [word 200, word 100], word 44), (26, [word 3, word 5], word 254),
    (27, [word 64, word 2], word (modulus - 128)), (27, [word (modulus - 128), word (modulus - 1)], word (modulus - 128)),
    (28, [word (modulus - 128), word (modulus - 1)], word (modulus - 128)), (28, [word (modulus - 7), word 2], word (modulus - 3)),
    (29, [word (modulus - 7), word 2], word (modulus - 1)), (29, [word (modulus - 128), word (modulus - 1)], word 0),
    (30, [word 7, word 2], word 3),
    (31, [word (2 ^ 255 - 1), word 1], word (2 ^ 255)), (32, [word 0, word 1], word (modulus - 1)),
    (33, [word (2 ^ 255), word (modulus - 1)], word (2 ^ 255)),
    -- At a mapping element, and on an open target that a later use types `uint8`.
    (34, [word 32767, word 1], word (modulus - 32768)), (35, [], word 44),
    -- Step 8c: two open literal operands wait for their type, from a later use, the return type
    -- or the `uint256` default, and wrap there; at `Word` they are Word's.
    (37, [], word 44), (38, [], word 3), (39, [], word 0), (40, [], boolean true),
    (41, [], word (modulus - 1))]
  for (index, arguments, expected) in cases do
    let completed ← execute session (← key index) arguments
    require (completed.value == expected)
      s!"{uncheckedNames[index]?} on {reprStr arguments} gave {reprStr completed.value}"
    session := completed.session
  -- A zero divisor panics with 0x12, `MIN / 0` too.
  for (index, arguments) in [(10, [word 7, word 0]), (11, [word 7, word 0]), (12, [word (modulus - 128), word 0]),
      (13, [word 5, word 0]), (14, [word 1, word 0]), (15, [word 1, word 0]),
      (28, [word (modulus - 128), word 0]), (29, [word 5, word 0]), (30, [word 7, word 0]), (33, [word 1, word 0])] do
    session ← panics session (← key index) arguments SourceCorePanics.divisionByZero
      s!"{uncheckedNames[index]?} on {reprStr arguments}"
  session ← panics session (← key 24) [word 255] SourceCorePanics.arithmetic "uscope8u after the block"
  -- An absent operand fails with the compound assignment's own diagnostic, naming the target's type.
  let uint8 ← match TypeSystem.FixedInteger.ofName? "uint8" with
    | some type => pure type | none => throw (IO.userError "uint8 missing")
  discard <| invalidOperands session (← key 36) [word 1]
    (.invalidAssignmentOperands .uncheckedAdd none (some (.fixed uint8))) "uabsentAdd8u"
  -- Both operands share the type, and unchecked arithmetic never takes `integer`.
  rejectedByInference "unchecked operands of different fixed-width types"
    ["function bad(x: uint8, y: uint16) returns (uint8) { unchecked { return x + y; } }"]
  rejectedByInference "unchecked + on a fixed-width type and Word"
    ["function bad(x: uint8, w: Word) returns (uint8) { unchecked { return x + w; } }"]
  -- An unchecked compound never takes `integer`, declared or resolved later.
  rejectedByInference "an unchecked += on integer"
    ["function bad(n: integer) returns (integer) { let r: integer = n; unchecked { r += 1; } return r; }"]
  match checkProgram (workspaceOf
      ["function bad() returns (Word) { let x = 0; unchecked { x += 1; } let y: integer = x; return 0; }"]) with
  | .error [.inference ⟨_, .compoundTargetNotSupported _ operator type⟩] =>
      require (operator == .uncheckedAdd && decide (type = TypeSystem.Ty.integer))
        s!"an integer unchecked compound target named {reprStr operator} and {reprStr type}"
  | .ok _ => throw (IO.userError "an integer unchecked compound target was accepted")
  | .error errors => throw (IO.userError s!"an integer unchecked compound target gave {reprStr errors}")
  -- An unchecked operator's open literal operands never take `integer`: finalization rejects
  -- one that a later use makes `integer`, with the diagnostic of an `integer` operand.
  match checkProgram (workspaceOf
      ["function bad() returns (Word) { unchecked { let a = 1 + 2; let b: integer = a; } return 0; }"]) with
  | .error [.inference ⟨_, .operatorNotSupported name type⟩] =>
      require (name == "UncheckedAdd" && decide (type = TypeSystem.Ty.integer))
        s!"an integer unchecked operand named {name} and {reprStr type}"
  | .ok _ => throw (IO.userError "an integer unchecked operand was accepted")
  | .error errors => throw (IO.userError s!"an integer unchecked operand gave {reprStr errors}")
  IO.println "SOURCE_CORE_FIXED_UNCHECKED_PASS: unchecked + - * wrapping modulo 2^N on the unsigned types and in two's complement on the signed ones with canonical results, unchecked / % rounding toward zero with MIN / -1 giving MIN and MIN % -1 giving 0, a zero divisor panicking with 0x12, -x in a block as unchecked 0 - x, literal operands typed by the other operand on either side, checked arithmetic again after the block, mixed operand types rejected, unchecked += -= *= /= %= on fixed-width locals, a mapping element and an open target typed later wrapping alike, with 0x12 on a zero divisor and its own diagnostic for an absent operand, an integer target rejected, two open literal operands typed by a later use, the return type or the uint256 default and wrapping there, and open literal operands that a later use makes integer rejected"

/-- Step 8d's fixture: `<<` and `>>` on the twelve types, by amounts of `Word`
and the unsigned types. -/
private def shiftWorkspace : Workspace.RawWorkspace := workspaceOf [
  "function shl8u(x: uint8, s: uint8) returns (uint8) { return x << s; }",
  "function shr8u(x: uint8, s: uint256) returns (uint8) { return x >> s; }",
  "function shl8s(x: int8, s: uint8) returns (int8) { return x << s; }",
  "function shr8s(x: int8, s: uint8) returns (int8) { return x >> s; }",
  "function shl16u(x: uint16, s: Word) returns (uint16) { return x << s; }",
  "function shl256s(x: int256, s: Word) returns (int256) { return x << s; }",
  "function shr256s(x: int256, s: uint16) returns (int256) { return x >> s; }",
  "function shl256u(x: uint256, s: uint8) returns (uint256) { return x << s; }",
  "function shr256u(x: uint256, s: uint256) returns (uint256) { return x >> s; }",
  "function shrWordBy8u(w: Word, s: uint8) returns (Word) { return w >> s; }",
  "function litAmount8u(x: uint8) returns (uint8) { return x << 3; }",
  "function litAmount8s(x: int8) returns (int8) { return x >> 1; }",
  "function litPast8u(x: uint8) returns (uint8) { return x << 300; }",
  "function litValue8u(s: uint8) returns (uint8) { return 1 << s; }",
  "function litValue8s(s: uint8) returns (int8) { return 1 << s; }",
  "function litBoth8u() returns (uint8) { return 1 << 7; }",
  "function openDefault() returns (bool) { let a = 1 << 255; return a > 5; }",
  "function openPast() returns (bool) { let a = 1 << 256; return a == 0; }",
  "function openWord() returns (Word) { let a = 1 << 3; let b: Word = a; return b; }",
  "function precedence8u(x: uint8) returns (uint8) { return x + 1 << 2; }",
  "function mask8u(x: uint8) returns (uint8) { return x & 0xF << 4; }",
  "function ushl8u(x: uint8, s: uint8) returns (uint8) { unchecked { return x << s; } }",
  "function ushr8s(x: int8, s: uint8) returns (int8) { unchecked { return x >> s; } }",
  "function compare8s(x: int8) returns (bool) { return x >> 1 < x; }"]

private def shiftNames : List String := [
  "shl8u", "shr8u", "shl8s", "shr8s", "shl16u", "shl256s", "shr256s", "shl256u", "shr256u", "shrWordBy8u",
  "litAmount8u", "litAmount8s", "litPast8u", "litValue8u", "litValue8s", "litBoth8u", "openDefault",
  "openPast", "openWord", "precedence8u", "mask8u", "ushl8u", "ushr8s", "compare8s"]

/-- Finalization rejects a shift whose value or amount has a type that no `Shl`
or `Shr` instance takes, naming the shift's function and that type. -/
private def rejectedShift (label name : String) (expected : TypeSystem.Ty) (lines : List String) : IO Unit :=
  match checkProgram (workspaceOf lines) with
  | .error [.inference ⟨_, .operatorNotSupported actual type⟩] =>
      require (actual == name && decide (type = expected)) s!"{label} named {actual} and {reprStr type}"
  | .ok _ => throw (IO.userError s!"{label} was accepted")
  | .error errors => throw (IO.userError s!"{label} gave {reprStr errors}")

/-- Step 8d, `<<` and `>>` on the twelve types, through the public API, as
upstream's `Shl` and `Shr` instances give them: `uintN <<` is Word's shift
masked to the low `N` bits, `intN <<` is Word's shift sign-extended from bit
`N - 1`, `uintN >>` is Word's shift and `intN >>` the arithmetic one, so an
amount of at least the width gives 0, or -1 for a negative value's `>>`, and
no shift panics. The amount takes its own type: `Word` or an unsigned type. -/
def runShifts : IO Unit := do
  let program ← get "fixed-width shift check" (checkProgram shiftWorkspace)
  let seeds ← shiftNames.mapM (seed program)
  let compiled ← get "fixed-width shift compilation"
    (compile shiftWorkspace seeds {specializationBudget := 256, compilationFuel := 1000})
  let key (index : Nat) : IO Key := match compiled.keys[index]? with
    | some key => pure key | none => throw (IO.userError "fixed-width shift root missing")
  let mut session ← boot (← compiled.open)
  let cases : List (Nat × List Value × Value) := [
    -- `uint8 <<` keeps the low 8 bits, and `>>` by a `uint256` amount is Word's.
    (0, [word 1, word 3], word 8), (0, [word 0x81, word 1], word 2), (0, [word 1, word 7], word 128),
    (0, [word 1, word 8], word 0), (0, [word 255, word 255], word 0), (0, [word 0xFF, word 4], word 0xF0),
    (1, [word 0x80, word 7], word 1), (1, [word 0xF0, word 4], word 0x0F), (1, [word 255, word 0], word 255),
    (1, [word 255, word 300], word 0), (1, [word 255, word (modulus - 1)], word 0),
    -- `int8 <<` sign-extends the low 8 bits; `>>` is arithmetic and gives -1 for a negative value
    -- past the width.
    (2, [word 1, word 7], word (modulus - 128)), (2, [word (modulus - 1), word 1], word (modulus - 2)),
    (2, [word 0x40, word 1], word (modulus - 128)), (2, [word 3, word 6], word (modulus - 64)),
    (2, [word (modulus - 128), word 1], word 0), (2, [word 1, word 8], word 0),
    (2, [word (modulus - 1), word 7], word (modulus - 128)),
    (3, [word (modulus - 128), word 1], word (modulus - 64)), (3, [word (modulus - 128), word 8], word (modulus - 1)),
    (3, [word 127, word 8], word 0), (3, [word 127, word 6], word 1), (3, [word 64, word 3], word 8),
    (3, [word (modulus - 5), word 1], word (modulus - 3)), (3, [word (modulus - 1), word 255], word (modulus - 1)),
    -- By a `Word` amount, up to `2^256 - 1`.
    (4, [word 0x8001, word 1], word 2), (4, [word 1, word 15], word 0x8000), (4, [word 1, word 16], word 0),
    (4, [word 1, word (modulus - 1)], word 0),
    (5, [word 1, word 255], word (2 ^ 255)), (5, [word 1, word 256], word 0), (5, [word 3, word 255], word (2 ^ 255)),
    (5, [word (modulus - 1), word 255], word (2 ^ 255)), (5, [word (modulus - 1), word 1], word (modulus - 2)),
    -- `int256 >>` by a `uint16` amount: `MIN >> 300` is -1.
    (6, [word (2 ^ 255), word 300], word (modulus - 1)), (6, [word (2 ^ 255), word 255], word (modulus - 1)),
    (6, [word (2 ^ 255), word 254], word (modulus - 2)), (6, [word (2 ^ 255 - 1), word 254], word 1),
    (6, [word (2 ^ 255 - 1), word 300], word 0), (6, [word (modulus - 8), word 2], word (modulus - 2)),
    (7, [word 1, word 255], word (2 ^ 255)), (7, [word (modulus - 1), word 1], word (modulus - 2)),
    (8, [word (2 ^ 255), word 255], word 1), (8, [word (modulus - 1), word 255], word 1),
    (8, [word (modulus - 1), word 256], word 0), (8, [word (modulus - 1), word (modulus - 1)], word 0),
    -- A `Word` value by a `uint8` amount.
    (9, [word (2 ^ 255), word 255], word 1), (9, [word 0x100, word 8], word 1),
    -- A literal amount defaults to `uint256`; `x << 300` is 0 at `uint8`.
    (10, [word 1], word 8), (10, [word 0x20], word 0), (10, [word 0x1F], word 0xF8),
    (11, [word (modulus - 5)], word (modulus - 3)), (11, [word 127], word 63),
    (12, [word 1], word 0), (12, [word 255], word 0),
    -- A literal value takes the return's type.
    (13, [word 7], word 128), (13, [word 8], word 0), (13, [word 0], word 1),
    (14, [word 7], word (modulus - 128)), (14, [word 6], word 64), (14, [word 8], word 0),
    (15, [], word 128),
    -- Open literals default to `uint256`, where `1 << 256` is 0, or take a later use's `Word`.
    (16, [], boolean true), (17, [], boolean true), (18, [], word 8),
    -- `x + 1 << 2` is `(x + 1) << 2`, and `x & 0xF << 4` is `x & (0xF << 4)`.
    (19, [word 1], word 8), (19, [word 2], word 12), (19, [word 63], word 0), (20, [word 0xAB], word 0xA0),
    -- In an `unchecked` block a shift is the same.
    (21, [word 0x81, word 1], word 2), (21, [word 255, word 4], word 0xF0),
    (22, [word (modulus - 128), word 1], word (modulus - 64)),
    -- `x >> 1 < x` compares signed.
    (23, [word (modulus - 128)], boolean false), (23, [word 5], boolean true), (23, [word (modulus - 1)], boolean false)]
  for (index, arguments, expected) in cases do
    let completed ← execute session (← key index) arguments
    require (completed.value == expected)
      s!"{shiftNames[index]?} on {reprStr arguments} gave {reprStr completed.value}"
    session := completed.session
  -- The amount is `Word` or an unsigned type, as upstream's `ShiftAmount` instances are: a signed
  -- amount is rejected, as upstream's `shift_by_signed_amount` fixture has it, and so are an
  -- `integer` or `Bool` amount and an `integer` value.
  rejectedShift "a signed amount" "shl" (.fixed ⟨true, .w8⟩)
    ["function bad(x: uint8, s: int8) returns (uint8) { return x << s; }"]
  rejectedShift "an int256 amount on Word" "shr" (.fixed ⟨true, .w256⟩)
    ["function bad(w: Word, s: int256) returns (Word) { return w >> s; }"]
  rejectedShift "an integer amount" "shr" .integer
    ["function bad(x: uint8, n: integer) returns (uint8) { return x >> n; }"]
  rejectedShift "a Bool amount" "shl" .bool
    ["function bad(x: uint8, b: Bool) returns (uint8) { return x << b; }"]
  rejectedShift "an integer value" "shl" .integer
    ["function bad(n: integer) returns (integer) { return n << 1; }"]
  -- A negative literal amount defaults to `uint256` and is out of its range, as upstream's.
  rejectedOutOfRange "a negative literal amount" "uint256" (-1)
    ["function bad(x: uint8) returns (uint8) { return x << -1; }"]
  -- A lambda parameter that only a shift's value types: local generalization quantifies it, so its
  -- type is still open at finalization, as for step 7b's compound targets.
  match checkProgram (workspaceOf
      ["function bad() returns (Word) { let f = lam(x) { return x << 1; }; return 0; }"]) with
  | .error [.inference ⟨_, .operatorNotSupported name (.variable _)⟩] =>
      require (name == "shl") s!"a generalized lambda's shift named {name}"
  | .ok _ => throw (IO.userError "a shift of a generalized lambda parameter was accepted")
  | .error errors => throw (IO.userError s!"a shift of a generalized lambda parameter gave {reprStr errors}")
  IO.println "SOURCE_CORE_FIXED_SHIFTS_PASS: << and >> on signed and unsigned fixed-width types by Word and unsigned amounts of other types, uintN << keeping the low N bits, intN << sign-extending them, uintN >> as Word's and intN >> arithmetic, amounts past the width giving 0 or -1 for a negative >>, no shift panicking, a Word value by a uint8 amount, literal amounts defaulted to uint256 and literal values typed by the return, open literals defaulted to uint256 or typed by a later use, precedence with + and &, shifts in an unchecked block, signed comparison of a shift's result, signed, integer and Bool amounts, an integer value, a negative literal amount and a generalized lambda parameter rejected"

/-- Step 8d's second fixture: `<<=` and `>>=` on the twelve types and Word, by
amounts of `Word` and the unsigned types, on locals, a mapping element, open
targets, in an `unchecked` block and in a `for` loop's header and body. -/
private def compoundShiftWorkspace : Workspace.RawWorkspace := workspaceOf [
  "function cshl8u(x: uint8, s: uint8) returns (uint8) { let r: uint8 = x; r <<= s; return r; }",
  "function cshr8u(x: uint8, s: uint256) returns (uint8) { let r: uint8 = x; r >>= s; return r; }",
  "function cshl8s(x: int8, s: uint8) returns (int8) { let r: int8 = x; r <<= s; return r; }",
  "function cshr8s(x: int8, s: uint8) returns (int8) { let r: int8 = x; r >>= s; return r; }",
  "function cshlWord(w: Word, s: Word) returns (Word) { let r: Word = w; r <<= s; return r; }",
  "function cshrWord(w: Word, s: uint8) returns (Word) { let r: Word = w; r >>= s; return r; }",
  "function clit8u(x: uint8) returns (uint8) { let r: uint8 = x; r <<= 3; return r; }",
  "function clitPast8u(x: uint8) returns (uint8) { let r: uint8 = x; r <<= 300; return r; }",
  "function cmapped8u(x: uint8, s: uint256) returns (uint8) { let m: mapping(Bool => uint8); m[true] = x; m[true] <<= s; return m[true]; }",
  "function copen8u() returns (uint8) { let x = 1; x <<= 7; return x; }",
  "function copenPast8u() returns (uint8) { let x = 1; x <<= 8; return x; }",
  "function copenDefault() returns (bool) { let x = 1; x <<= 255; return x > 5; }",
  "function copenWord() returns (Word) { let x = 1; x <<= 3; let w: Word = x; return w; }",
  "function cunchecked8u(x: uint8, s: uint8) returns (uint8) { let r: uint8 = x; unchecked { r <<= s; } return r; }",
  "function cforPost8u(x: uint8) returns (uint8) { let r: uint8 = x; for (let i: Word = 0; i < 2; r <<= 1) { i += 1; } return r; }",
  "function cforBody(w: Word, s: uint8) returns (Word) { let r: Word = w; for (let i: Word = 0; i < 2; i += 1) { r >>= s; } return r; }"]

private def compoundShiftNames : List String := [
  "cshl8u", "cshr8u", "cshl8s", "cshr8s", "cshlWord", "cshrWord", "clit8u", "clitPast8u", "cmapped8u",
  "copen8u", "copenPast8u", "copenDefault", "copenWord", "cunchecked8u", "cforPost8u", "cforBody"]

/-- Step 8d, `<<=` and `>>=`, through the public API, as upstream's rewrite of
`x <<= n` to `x = x << n` gives them: the target is the shift's value and keeps
its type, the amount takes its own, `Word` or an unsigned type, and the meaning
is `runShifts`' shift written back. -/
def runCompoundShifts : IO Unit := do
  let program ← get "compound shift check" (checkProgram compoundShiftWorkspace)
  let seeds ← compoundShiftNames.mapM (seed program)
  let compiled ← get "compound shift compilation"
    (compile compoundShiftWorkspace seeds {specializationBudget := 256, compilationFuel := 1000})
  let key (index : Nat) : IO Key := match compiled.keys[index]? with
    | some key => pure key | none => throw (IO.userError "compound shift root missing")
  let mut session ← boot (← compiled.open)
  let cases : List (Nat × List Value × Value) := [
    -- `uint8 <<=` keeps the low 8 bits, and `>>=` by a `uint256` amount is Word's.
    (0, [word 1, word 3], word 8), (0, [word 0x81, word 1], word 2), (0, [word 1, word 8], word 0),
    (0, [word 255, word 255], word 0),
    (1, [word 0x80, word 7], word 1), (1, [word 255, word 300], word 0), (1, [word 0xF0, word 4], word 0x0F),
    -- `int8 <<=` sign-extends the low 8 bits, and `>>=` is arithmetic.
    (2, [word 1, word 7], word (modulus - 128)), (2, [word (modulus - 1), word 1], word (modulus - 2)),
    (2, [word 1, word 8], word 0),
    (3, [word (modulus - 128), word 1], word (modulus - 64)), (3, [word (modulus - 128), word 8], word (modulus - 1)),
    (3, [word 127, word 8], word 0), (3, [word 64, word 3], word 8),
    -- A `Word` target by a `Word` amount and by a `uint8` one.
    (4, [word 1, word 255], word (2 ^ 255)), (4, [word 1, word 256], word 0), (4, [word 3, word 1], word 6),
    (5, [word (2 ^ 255), word 255], word 1), (5, [word 0x100, word 8], word 1),
    -- A literal amount defaults to `uint256`; `r <<= 300` is 0 at `uint8`.
    (6, [word 1], word 8), (6, [word 0x20], word 0), (6, [word 0x1F], word 0xF8), (7, [word 255], word 0),
    -- A mapping element of `uint8`.
    (8, [word 1, word 7], word 128), (8, [word 3, word 7], word 128), (8, [word 1, word 8], word 0),
    -- An open target takes a later use's type, the return's `uint8` or a `Word`, or defaults to `uint256`.
    (9, [], word 128), (10, [], word 0), (11, [], boolean true), (12, [], word 8),
    -- In an `unchecked` block a compound shift is the same.
    (13, [word 0x81, word 1], word 2), (13, [word 255, word 4], word 0xF0),
    -- In a `for` loop's header and body.
    (14, [word 3], word 12), (14, [word 0x81], word 4),
    (15, [word 0x100, word 4], word 1), (15, [word 0xFF, word 1], word 0x3F)]
  for (index, arguments, expected) in cases do
    let completed ← execute session (← key index) arguments
    require (completed.value == expected)
      s!"{compoundShiftNames[index]?} on {reprStr arguments} gave {reprStr completed.value}"
    session := completed.session
  -- The amount is `Word` or an unsigned type, as for `<<`: a signed, `integer` or `Bool` amount is
  -- rejected, and so is an open amount that a later use makes signed.
  rejectedShift "a signed <<= amount" "shl" (.fixed ⟨true, .w8⟩)
    ["function bad(x: uint8, s: int8) returns (uint8) { let r: uint8 = x; r <<= s; return r; }"]
  rejectedShift "an integer >>= amount" "shr" .integer
    ["function bad(w: Word, n: integer) returns (Word) { let r: Word = w; r >>= n; return r; }"]
  rejectedShift "a Bool <<= amount" "shl" .bool
    ["function bad(x: uint8, b: Bool) returns (uint8) { let r: uint8 = x; r <<= b; return r; }"]
  rejectedShift "an open amount made int8" "shl" (.fixed ⟨true, .w8⟩)
    ["function bad(x: uint8) returns (uint8) { let r: uint8 = x; let n = 1; r <<= n; let m: int8 = n; return r; }"]
  -- The target is the shift's value: an `integer` or `Bool` target is rejected, and so is an open
  -- one that a later use makes `integer`.
  rejectedByInference "<<= on integer"
    ["function bad(n: integer) returns (integer) { let r: integer = n; r <<= 1; return r; }"]
  rejectedByInference ">>= on Bool"
    ["function bad(b: Bool) returns (Bool) { let r: Bool = b; r >>= 1; return r; }"]
  match checkProgram (workspaceOf
      ["function bad() returns (Word) { let x = 1; x <<= 2; let y: integer = x; return 0; }"]) with
  | .error [.inference ⟨_, .compoundTargetNotSupported _ operator type⟩] =>
      require (operator == .shiftLeft && decide (type = TypeSystem.Ty.integer))
        s!"an integer <<= target named {reprStr operator} and {reprStr type}"
  | .ok _ => throw (IO.userError "an integer <<= target was accepted")
  | .error errors => throw (IO.userError s!"an integer <<= target gave {reprStr errors}")
  IO.println "SOURCE_CORE_FIXED_COMPOUND_SHIFTS_PASS: <<= and >>= on signed and unsigned fixed-width locals and Word by Word and unsigned amounts of other types, uintN <<= keeping the low N bits, intN <<= sign-extending them and intN >>= arithmetic, literal amounts defaulted to uint256, a uint8 mapping element, open targets typed by a later use or defaulted to uint256, compound shifts in an unchecked block and in a for loop's header and body, signed, integer and Bool amounts, an open amount made signed, integer and Bool targets and an open target made integer rejected"

/-- Step 9a's fixture: in-place `~` (`x ~=;`) on the twelve fixed-width types and
`Word`, on locals, mapping elements, open targets, in an `unchecked` block and
in a `for` loop's header and body. -/
private def bitNotWorkspace : Workspace.RawWorkspace := workspaceOf [
  "function not256u(x: uint256) returns (uint256) { let r: uint256 = x; r ~=; return r; }",
  "function not8s(x: int8) returns (int8) { let r: int8 = x; r ~=; return r; }",
  "function not16s(x: int16) returns (int16) { let r: int16 = x; r ~=; return r; }",
  "function not32s(x: int32) returns (int32) { let r: int32 = x; r ~=; return r; }",
  "function not64s(x: int64) returns (int64) { let r: int64 = x; r ~=; return r; }",
  "function not128s(x: int128) returns (int128) { let r: int128 = x; r ~=; return r; }",
  "function not256s(x: int256) returns (int256) { let r: int256 = x; r ~=; return r; }",
  "function notWord(w: Word) returns (Word) { let r: Word = w; r ~=; return r; }",
  "function notMapped8s(x: int8) returns (int8) { let m: mapping(Bool => int8); m[true] = x; m[true] ~=; return m[true]; }",
  "function notOpenDefault() returns (bool) { let x = 0; x ~=; return x > 5; }",
  "function notOpenLater8s() returns (int8) { let x = 5; x ~=; let y: int8 = x; return y; }",
  "function notOpenReturn256s() returns (int256) { let x = 0; x ~=; return x; }",
  "function notOpenWord() returns (Word) { let x = 1; x ~=; let w: Word = x; return w; }",
  "function notTwice8s(x: int8) returns (int8) { let r: int8 = x; r ~=; r ~=; return r; }",
  "function notForPost8s(x: int8) returns (int8) { let r: int8 = x; for (let i: Word = 0; i < 1; r ~=) { i += 1; } return r; }",
  "function notForBody256u(x: uint256) returns (uint256) { let r: uint256 = x; for (let i: Word = 0; i < 3; i += 1) { r ~=; } return r; }",
  "function not8u(x: uint8) returns (uint8) { let r: uint8 = x; r ~=; return r; }",
  "function not16u(x: uint16) returns (uint16) { let r: uint16 = x; r ~=; return r; }",
  "function not32u(x: uint32) returns (uint32) { let r: uint32 = x; r ~=; return r; }",
  "function not64u(x: uint64) returns (uint64) { let r: uint64 = x; r ~=; return r; }",
  "function not128u(x: uint128) returns (uint128) { let r: uint128 = x; r ~=; return r; }",
  "function notMapped8u(x: uint8) returns (uint8) { let m: mapping(Bool => uint8); m[true] = x; m[true] ~=; return m[true]; }",
  "function notOpenLater8u() returns (uint8) { let x = 5; x ~=; let y: uint8 = x; return y; }",
  "function notTwice16u(x: uint16) returns (uint16) { let r: uint16 = x; r ~=; r ~=; return r; }",
  "function notUnchecked8u(x: uint8) returns (uint8) { let r: uint8 = x; unchecked { r ~=; } return r; }",
  "function notForPost8u(x: uint8) returns (uint8) { let r: uint8 = x; for (let i: Word = 0; i < 1; r ~=) { i += 1; } return r; }",
  "function notSum8u(x: uint8) returns (uint8) { let r: uint8 = x; r ~=; return r + x; }"]

private def bitNotNames : List String := [
  "not256u", "not8s", "not16s", "not32s", "not64s", "not128s", "not256s", "notWord", "notMapped8s",
  "notOpenDefault", "notOpenLater8s", "notOpenReturn256s", "notOpenWord", "notTwice8s", "notForPost8s",
  "notForBody256u", "not8u", "not16u", "not32u", "not64u", "not128u", "notMapped8u", "notOpenLater8u",
  "notTwice16u", "notUnchecked8u", "notForPost8u", "notSum8u"]

/-- Finalization rejects an in-place `~` whose target has a type that no
`BitNot` instance takes, naming the trait and that type. -/
private def rejectedBitNot (label : String) (expected : TypeSystem.Ty) (lines : List String) : IO Unit :=
  match checkProgram (workspaceOf lines) with
  | .error [.inference ⟨_, .operatorNotSupported actual type⟩] =>
      require (actual == "BitNot" && decide (type = expected)) s!"{label} named {actual} and {reprStr type}"
  | .ok _ => throw (IO.userError s!"{label} was accepted")
  | .error errors => throw (IO.userError s!"{label} gave {reprStr errors}")

/-- Step 9a, in-place `~`, through the public API, as upstream's rewrite of `x ~=`
to `x = ~x` gives it: the target keeps its type and takes that type's `~`, the
low `N` bits of Word's on `uint8` … `uint128`, and Word's on `uint256`, the
signed types and `Word`; an open target waits for its type and defaults to
`uint256`. The place is evaluated once. -/
def runBitNotAssignments : IO Unit := do
  let program ← get "bit-not check" (checkProgram bitNotWorkspace)
  let seeds ← bitNotNames.mapM (seed program)
  let compiled ← get "bit-not compilation"
    (compile bitNotWorkspace seeds {specializationBudget := 256, compilationFuel := 1000})
  let key (index : Nat) : IO Key := match compiled.keys[index]? with
    | some key => pure key | none => throw (IO.userError "bit-not root missing")
  let max := modulus - 1
  let mut session ← boot (← compiled.open)
  let cases : List (Nat × List Value × Value) := [
    -- `uint256` is Word's `~`.
    (0, [word 5], word (modulus - 6)), (0, [word 0], word max), (0, [word max], word 0),
    -- On the signed types `~x` is `-x - 1`, sign-extended.
    (1, [word 5], word (modulus - 6)), (1, [word max], word 0), (1, [word (modulus - 128)], word 127),
    (1, [word 127], word (modulus - 128)),
    (2, [word 0], word max), (2, [word 32767], word (modulus - 32768)),
    (3, [word (modulus - 2 ^ 31)], word (2 ^ 31 - 1)),
    (4, [word 1], word (modulus - 2)),
    (5, [word (2 ^ 127 - 1)], word (modulus - 2 ^ 127)),
    (6, [word 0], word max), (6, [word (2 ^ 255 - 1)], word (2 ^ 255)),
    -- A `Word` target, as before.
    (7, [word 0], word max), (7, [word 0xff], word (max - 0xff)),
    -- A mapping element of `int8`.
    (8, [word 5], word (modulus - 6)),
    -- An open target defaults to `uint256`, or takes a later use's `int8`, the return's `int256` or a `Word`.
    (9, [], boolean true), (10, [], word (modulus - 6)), (11, [], word max), (12, [], word (max - 1)),
    -- Twice is the identity; in a `for` loop's header and body.
    (13, [word (modulus - 3)], word (modulus - 3)), (14, [word 5], word (modulus - 6)),
    (15, [word 5], word (max - 5)),
    -- On `uint8` … `uint128` the low `N` bits of Word's `~`.
    (16, [word 0], word 255), (16, [word 255], word 0), (16, [word 0x0F], word 0xF0),
    (17, [word 0], word 0xFFFF), (17, [word 0x1234], word 0xEDCB),
    (18, [word 1], word 0xFFFFFFFE),
    (19, [word 0], word (2 ^ 64 - 1)),
    (20, [word (2 ^ 128 - 1)], word 0), (20, [word 0], word (2 ^ 128 - 1)),
    -- A mapping element of `uint8`, an open target typed `uint8` by a later use, twice, in an
    -- `unchecked` block, in a `for` loop's post clause, and a result that checked `+` adds to.
    (21, [word 5], word 250), (22, [], word 250), (23, [word 0x1234], word 0x1234),
    (24, [word 0x0F], word 0xF0), (25, [word 5], word 250), (26, [word 0x0F], word 255)]
  for (index, arguments, expected) in cases do
    let completed ← execute session (← key index) arguments
    require (completed.value == expected)
      s!"{bitNotNames[index]?} on {reprStr arguments} gave {reprStr completed.value}"
    session := completed.session
  -- Upstream defines no `BitNot` on `integer` or `Bool`: a closed target of those types fails to
  -- unify with `Word`, and an open one that a later use makes `integer` is rejected at finalization.
  rejectedByInference "~= on integer"
    ["function bad(n: integer) returns (integer) { let r: integer = n; r ~=; return r; }"]
  rejectedByInference "~= on Bool"
    ["function bad(b: Bool) returns (Bool) { let r: Bool = b; r ~=; return r; }"]
  rejectedBitNot "an open ~= target made integer" .integer
    ["function bad() returns (Word) { let x = 1; x ~=; let y: integer = x; return 0; }"]
  IO.println "SOURCE_CORE_FIXED_BIT_NOT_ASSIGNMENTS_PASS: in-place ~ on the twelve fixed-width types and Word, keeping the low N bits on uint8 … uint128 and as Word's ~ elsewhere, sign-extended on the signed types, on locals, int8 and uint8 mapping elements, in an unchecked block and in a for loop's header and body, with canonical results, open targets defaulted to uint256 or typed by a later use, the return or a Word, integer and Bool targets and an open target made integer rejected"

/-- Step 9b's first part: `uint256(w)`, `uintN(w)` and `intN(w)`, a word as a
value of one of the twelve types. -/
private def conversionWorkspace : Workspace.RawWorkspace := workspaceOf [
  "function toU8(w: Word) returns (uint8) { return uint8(w); }",
  "function toU16(w: Word) returns (uint16) { return uint16(w); }",
  "function toU32(w: Word) returns (uint32) { return uint32(w); }",
  "function toU64(w: Word) returns (uint64) { return uint64(w); }",
  "function toU128(w: Word) returns (uint128) { return uint128(w); }",
  "function toU256(w: Word) returns (uint256) { return uint256(w); }",
  "function toI8(w: Word) returns (int8) { return int8(w); }",
  "function toI16(w: Word) returns (int16) { return int16(w); }",
  "function toI32(w: Word) returns (int32) { return int32(w); }",
  "function toI64(w: Word) returns (int64) { return int64(w); }",
  "function toI128(w: Word) returns (int128) { return int128(w); }",
  "function toI256(w: Word) returns (int256) { return int256(w); }",
  "function literalU8() returns (uint8) { return uint8(255); }",
  "function literalI8() returns (int8) { return int8(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff); }",
  "function dirtyU8() returns (uint8) { return uint8(256); }",
  "function dirtyI8() returns (int8) { return int8(128); }",
  "function openTarget(w: Word) returns (uint16) { let x = uint16(w); return x; }",
  "function checkedAfter(w: Word) returns (uint8) { let x: uint8 = uint8(w); return x + 1; }",
  "function bothBranches(w: Word, flag: Bool) returns (int16) { if (flag) { return int16(w); } else { return int16(0); } }"]

private def conversionNames : List String := [
  "toU8", "toU16", "toU32", "toU64", "toU128", "toU256", "toI8", "toI16", "toI32", "toI64", "toI128",
  "toI256", "literalU8", "literalI8", "dirtyU8", "dirtyI8", "openTarget", "checkedAfter", "bothBranches"]

/-- A run that reverts with `DirtyHigherBitsForInteger()`: the reason is the
reserved one, the diagnostic decodes it, and the revert data is upstream's. -/
private def dirty {artifact : Artifact} (session : Session artifact) (key : Key) (arguments : List Value)
    (label : String) : IO (Session artifact) := do
  let executed ← session.runWithReceipt key arguments {executionFuel := 300000}
  match executed.val with
  | .ok (.failed reason next) =>
      require (reason == SourceCorePanics.dirtyReason) s!"{label} failed with {reprStr reason}"
      match session.diagnostic key reason with
      | .ok (some diagnostic) =>
          require (decide (diagnostic.error = .dirtyHigherBitsForInteger)) s!"{label} decoded {reprStr diagnostic.error}"
      | other => throw (IO.userError s!"{label} decoded {reprStr other}")
      require (SourceCorePanics.dirtyRevertData.toList == [0x6c, 0xc5, 0x4a, 0x63])
        s!"{label} revert data {reprStr SourceCorePanics.dirtyRevertData.toList}"
      pure next
  | .ok (.succeeded result) => throw (IO.userError s!"{label} gave {reprStr result.value}")
  | .ok _ => throw (IO.userError s!"{label} did not fail")
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")

/-- Step 9b's first part through the public API: a word canonical for its type
is that type's value, `uint256(w)` and `int256(w)` never fail, and any other
word reverts with `DirtyHigherBitsForInteger()`, as upstream's ABI decoders check
it, where upstream's `uintN(w)` keeps the raw word. -/
def runConversions : IO Unit := do
  let program ← get "conversion check" (checkProgram conversionWorkspace)
  let seeds ← conversionNames.mapM (seed program)
  let compiled ← get "conversion compilation"
    (compile conversionWorkspace seeds {specializationBudget := 256, compilationFuel := 1000})
  let key (name : String) : IO Key := match conversionNames.findIdx? (· == name) with
    | some index => match compiled.keys[index]? with
      | some key => pure key
      | none => throw (IO.userError s!"conversion root {name} missing")
    | none => throw (IO.userError s!"conversion {name} unknown")
  let max := modulus - 1
  let mut session ← boot (← compiled.open)
  let cases : List (String × List Value × Value) := [
    -- Canonical words at each unsigned type: up to `2^N - 1`.
    ("toU8", [word 0], word 0), ("toU8", [word 255], word 255),
    ("toU16", [word 65535], word 65535), ("toU32", [word (2 ^ 32 - 1)], word (2 ^ 32 - 1)),
    ("toU64", [word (2 ^ 64 - 1)], word (2 ^ 64 - 1)), ("toU128", [word (2 ^ 128 - 1)], word (2 ^ 128 - 1)),
    -- `uint256(w)` never fails.
    ("toU256", [word 0], word 0), ("toU256", [word max], word max),
    -- Canonical words at each signed type: the sign extension of the low `N` bits.
    ("toI8", [word 127], word 127), ("toI8", [word max], word max), ("toI8", [word (modulus - 128)], word (modulus - 128)),
    ("toI16", [word (modulus - 32768)], word (modulus - 32768)), ("toI32", [word (2 ^ 31 - 1)], word (2 ^ 31 - 1)),
    ("toI64", [word (modulus - 2 ^ 63)], word (modulus - 2 ^ 63)),
    ("toI128", [word (2 ^ 127 - 1)], word (2 ^ 127 - 1)),
    -- `int256(w)` never fails.
    ("toI256", [word (2 ^ 255)], word (2 ^ 255)), ("toI256", [word max], word max),
    -- Literal arguments are words: `uint8(255)`, and `int8(2^256 - 1)` is -1.
    ("literalU8", [], word 255), ("literalI8", [], word max),
    -- An open local takes the conversion's type; checked `+` follows it.
    ("openTarget", [word 7], word 7), ("checkedAfter", [word 254], word 255),
    ("bothBranches", [word (modulus - 1), boolean true], word max), ("bothBranches", [word 5, boolean false], word 0)]
  for (name, arguments, expected) in cases do
    let completed ← execute session (← key name) arguments
    require (completed.value == expected) s!"{name} on {reprStr arguments} gave {reprStr completed.value}"
    session := completed.session
  -- Non-canonical words revert, one past each edge.
  session ← dirty session (← key "dirtyU8") [] "uint8(256)"
  session ← dirty session (← key "dirtyI8") [] "int8(128)"
  session ← dirty session (← key "toU8") [word 256] "uint8 of 256"
  session ← dirty session (← key "toU16") [word 65536] "uint16 of 2^16"
  session ← dirty session (← key "toU32") [word (2 ^ 32)] "uint32 of 2^32"
  session ← dirty session (← key "toU64") [word (2 ^ 64)] "uint64 of 2^64"
  session ← dirty session (← key "toU128") [word max] "uint128 of 2^256 - 1"
  session ← dirty session (← key "toI8") [word 128] "int8 of 128"
  session ← dirty session (← key "toI8") [word (modulus - 129)] "int8 of -129"
  session ← dirty session (← key "toI16") [word 32768] "int16 of 2^15"
  session ← dirty session (← key "toI32") [word (modulus - 2 ^ 31 - 1)] "int32 of -2^31 - 1"
  session ← dirty session (← key "toI64") [word (2 ^ 63)] "int64 of 2^63"
  session ← dirty session (← key "toI128") [word (2 ^ 128)] "int128 of 2^128"
  -- A dirty word reverts before checked `+` could panic.
  session ← dirty session (← key "checkedAfter") [word 256] "checked + after uint8 of 256"
  let _ := session
  -- A conversion takes a `Word`: no other type converts.
  rejectedByInference "uint8 of a uint16"
    ["function bad(x: uint16) returns (uint8) { return uint8(x); }"]
  rejectedByInference "uint8 to the wrong type"
    ["function bad(w: Word) returns (uint16) { return uint8(w); }"]
  IO.println "SOURCE_CORE_FIXED_CONVERSIONS_PASS: uint256(w), uintN(w) and intN(w) through the public API, canonical words at each of the twelve types kept, uint256 and int256 never failing, literal words as arguments, an open local and checked + after a conversion, every other word reverting with DirtyHigherBitsForInteger() and upstream's revert data 0x6cc54a63, a non-Word argument and a wrong result type rejected"

/-- Step 9b's second part: `Typedef.abs` and `Typedef.rep`, chosen by the type
known at the call: the expected type for `abs` and the argument's type for
`rep`. -/
private def typedefWorkspace : Workspace.RawWorkspace := workspaceOf [
  "function absU8(w: Word) returns (uint8) { let x: uint8 = Typedef.abs(w); return x; }",
  "function absI16(w: Word) returns (int16) { return Typedef.abs(w); }",
  "function absU256(w: Word) returns (uint256) { return Typedef.abs(w); }",
  "function absI256(w: Word) returns (int256) { return Typedef.abs(w); }",
  "function absWord(w: Word) returns (Word) { let v: Word = Typedef.abs(w); return v; }",
  "function absAssigned(w: Word) returns (uint16) { let x: uint16 = 0; x = Typedef.abs(w); return x; }",
  "function absLiteral() returns (uint8) { return Typedef.abs(255); }",
  "function dirtyLiteral() returns (int8) { return Typedef.abs(128); }",
  "function repU8(x: uint8) returns (Word) { return Typedef.rep(x); }",
  "function repI8(x: int8) returns (Word) { let w: Word = Typedef.rep(x); return w; }",
  "function repU256(x: uint256) returns (Word) { return Typedef.rep(x); }",
  "function repWord(w: Word) returns (Word) { return Typedef.rep(w); }",
  "function repOpen(x: int64) returns (Word) { let w = Typedef.rep(x); return w; }",
  "function repSum(a: uint8, b: uint8) returns (Word) { return Typedef.rep(a) + Typedef.rep(b); }",
  "function roundTrip(x: int32) returns (int32) { return Typedef.abs(Typedef.rep(x)); }",
  "function narrowed(x: uint256) returns (uint8) { return Typedef.abs(Typedef.rep(x)); }"]

private def typedefNames : List String := [
  "absU8", "absI16", "absU256", "absI256", "absWord", "absAssigned", "absLiteral", "dirtyLiteral", "repU8",
  "repI8", "repU256", "repWord", "repOpen", "repSum", "roundTrip", "narrowed"]

/-- Inference rejects a `Typedef` call whose type is not known at the call or is
neither `Word` nor one of the twelve types, naming `Typedef` and that type. -/
private def rejectedTypedef (label : String) (expected : TypeSystem.Ty → Bool) (lines : List String) :
    IO Unit :=
  match checkProgram (workspaceOf lines) with
  | .error [.inference ⟨_, .operatorNotSupported actual type⟩] =>
      require (actual == "Typedef" && expected type) s!"{label} named {actual} and {reprStr type}"
  | .ok _ => throw (IO.userError s!"{label} was accepted")
  | .error errors => throw (IO.userError s!"{label} gave {reprStr errors}")

private def openType : TypeSystem.Ty → Bool
  | .variable _ => true
  | _ => false

/-- Step 9b's second part through the public API: `Typedef.abs` at one of the
twelve types is that type's conversion, and at `Word` the word itself;
`Typedef.rep` gives a value's word. A type that is not known at the call is
rejected, as is any other type. -/
def runTypedef : IO Unit := do
  let program ← get "Typedef check" (checkProgram typedefWorkspace)
  let seeds ← typedefNames.mapM (seed program)
  let compiled ← get "Typedef compilation"
    (compile typedefWorkspace seeds {specializationBudget := 256, compilationFuel := 1000})
  let key (name : String) : IO Key := match typedefNames.findIdx? (· == name) with
    | some index => match compiled.keys[index]? with
      | some key => pure key
      | none => throw (IO.userError s!"Typedef root {name} missing")
    | none => throw (IO.userError s!"Typedef function {name} unknown")
  let max := modulus - 1
  let mut session ← boot (← compiled.open)
  let cases : List (String × List Value × Value) := [
    -- `Typedef.abs` at an annotated `let`, a return, an assignment and a literal argument.
    ("absU8", [word 255], word 255), ("absI16", [word (modulus - 32768)], word (modulus - 32768)),
    ("absU256", [word max], word max), ("absI256", [word (2 ^ 255)], word (2 ^ 255)),
    ("absWord", [word max], word max), ("absAssigned", [word 65535], word 65535),
    ("absLiteral", [], word 255),
    -- `Typedef.rep` gives the value's word, sign-extended at the signed types.
    ("repU8", [word 200], word 200), ("repI8", [word max], word max), ("repU256", [word max], word max),
    ("repWord", [word 7], word 7), ("repOpen", [word (modulus - 2 ^ 63)], word (modulus - 2 ^ 63)),
    ("repSum", [word 255, word 255], word 510),
    ("roundTrip", [word (modulus - 5)], word (modulus - 5)), ("narrowed", [word 255], word 255)]
  for (name, arguments, expected) in cases do
    let completed ← execute session (← key name) arguments
    require (completed.value == expected) s!"{name} on {reprStr arguments} gave {reprStr completed.value}"
    session := completed.session
  -- `Typedef.abs` at a type below 256 bits checks the word as `uintN(w)` and `intN(w)` do.
  session ← dirty session (← key "absU8") [word 256] "Typedef.abs at uint8 of 256"
  session ← dirty session (← key "absI16") [word 32768] "Typedef.abs at int16 of 2^15"
  session ← dirty session (← key "absAssigned") [word 65536] "Typedef.abs assigned at uint16 of 2^16"
  session ← dirty session (← key "dirtyLiteral") [] "Typedef.abs at int8 of 128"
  session ← dirty session (← key "narrowed") [word 256] "Typedef.abs at uint8 of a uint256's word"
  let _ := session
  -- A type that is not known at the call waits for nothing: it is rejected.
  rejectedTypedef "Typedef.abs into an open local" openType
    ["function bad(w: Word) returns (uint8) { let a = Typedef.abs(w); let b: uint8 = a; return b; }"]
  rejectedTypedef "Typedef.abs as an argument" openType
    ["function take(x: uint8) returns (uint8) { return x; }",
     "function bad(w: Word) returns (uint8) { return take(Typedef.abs(w)); }"]
  rejectedTypedef "Typedef.rep of an open local" openType
    ["function bad() returns (Word) { let a = 5; return Typedef.rep(a); }"]
  rejectedTypedef "Typedef.rep of a literal" openType
    ["function bad() returns (Word) { return Typedef.rep(5); }"]
  -- Any other type is rejected.
  rejectedTypedef "Typedef.abs at Bool" (· == TypeSystem.Ty.bool)
    ["function bad(w: Word) returns (Bool) { return Typedef.abs(w); }"]
  rejectedTypedef "Typedef.rep of a Bool" (· == TypeSystem.Ty.bool)
    ["function bad(b: Bool) returns (Word) { return Typedef.rep(b); }"]
  rejectedTypedef "Typedef.rep of an integer" (· == TypeSystem.Ty.integer)
    ["function bad() returns (Word) { let i: integer = 1; return Typedef.rep(i); }"]
  -- `abs` takes a `Word`, one argument, and the two names are the only ones.
  rejectedByInference "Typedef.abs of a uint8"
    ["function bad(x: uint8) returns (uint16) { return Typedef.abs(x); }"]
  rejectedByInference "Typedef.abs of two words"
    ["function bad(w: Word) returns (uint8) { return Typedef.abs(w, w); }"]
  rejectedByInference "another Typedef name"
    ["function bad(w: Word) returns (Word) { return Typedef.other(w); }"]
  rejectedByInference "Typedef.abs as a value"
    ["function bad() returns (Word) { let f = Typedef.abs; return 0; }"]
  IO.println "SOURCE_CORE_TYPEDEF_PASS: Typedef.abs and Typedef.rep through the public API, chosen by the type known at the call, abs at the twelve types checking the word as uintN(w) and intN(w) do and at Word the word itself, rep giving a value's word, an abs or rep whose type is open at the call rejected naming Typedef, as are Bool and integer, a non-Word abs argument, two arguments, another name and Typedef.abs as a value"

/-- Step 9b's third part: `case uint256(p)`, which a `uint256` value's word is
matched with, as upstream's `enum uint256 { uint256(word) }` gives it. -/
private def uint256PatternWorkspace : Workspace.RawWorkspace := workspaceOf [
  "function unwrap(x: uint256) returns (Word) { match (x) { case uint256(w) { return w; } } }",
  "function plusOne(x: uint256) returns (uint256) { match (x) { case uint256(w) { return uint256(w + 1); } } }",
  "function isZero(x: uint256) returns (Bool) { match (x) { case uint256(0) { return true; } case _ { return false; } } }",
  "function ignored(x: uint256) returns (Word) { match (x) { case uint256(_) { return 7; } } }",
  "function grouped(x: uint256) returns (Word) { match (x) { case uint256((w)) { return w; } } }",
  "function pair(x: uint256, y: uint256) returns (Word) { match (x, y) { case (uint256(a), uint256(b)) { return a + b; } } }",
  "function opened() returns (Word) { let x = 5; match (x) { case uint256(w) { return w; } } }"]

private def uint256PatternNames : List String :=
  ["unwrap", "plusOne", "isZero", "ignored", "grouped", "pair", "opened"]

/-- Step 9b's third part through the public API: every `uint256` value matches
`uint256(w)`, which binds its word; a literal inside matches that word; and the
pattern at another type, or another type's spelling, is rejected as upstream
rejects it. -/
def runUint256Patterns : IO Unit := do
  let program ← get "uint256 pattern check" (checkProgram uint256PatternWorkspace)
  let seeds ← uint256PatternNames.mapM (seed program)
  let compiled ← get "uint256 pattern compilation"
    (compile uint256PatternWorkspace seeds {specializationBudget := 256, compilationFuel := 1000})
  let key (name : String) : IO Key := match uint256PatternNames.findIdx? (· == name) with
    | some index => match compiled.keys[index]? with
      | some key => pure key
      | none => throw (IO.userError s!"uint256 pattern root {name} missing")
    | none => throw (IO.userError s!"uint256 pattern {name} unknown")
  let max := modulus - 1
  let mut session ← boot (← compiled.open)
  let cases : List (String × List Value × Value) := [
    ("unwrap", [word 0], word 0), ("unwrap", [word max], word max),
    ("plusOne", [word 41], word 42), ("plusOne", [word max], word 0),
    ("isZero", [word 0], boolean true), ("isZero", [word 1], boolean false),
    ("ignored", [word 3], word 7), ("grouped", [word 9], word 9),
    ("pair", [word 2, word 3], word 5), ("opened", [], word 5)]
  for (name, arguments, expected) in cases do
    let completed ← execute session (← key name) arguments
    require (completed.value == expected) s!"{name} on {reprStr arguments} gave {reprStr completed.value}"
    session := completed.session
  let _ := session
  -- Upstream rejects a constructor pattern at the other eleven types and `uint256(w)` at another type.
  rejectedByInference "uint8(w) at uint8"
    ["function bad(x: uint8) returns (Word) { match (x) { case uint8(w) { return w; } } }"]
  rejectedByInference "int256(w) at int256"
    ["function bad(x: int256) returns (Word) { match (x) { case int256(w) { return w; } } }"]
  rejectedByInference "uint256(w) at Word"
    ["function bad(x: Word) returns (Word) { match (x) { case uint256(w) { return w; } } }"]
  rejectedByInference "uint256(w) at uint8"
    ["function bad(x: uint8) returns (Word) { match (x) { case uint256(w) { return w; } } }"]
  rejectedByInference "uint256 with two patterns"
    ["function bad(x: uint256) returns (Word) { match (x) { case uint256(a, b) { return a; } } }"]
  IO.println "SOURCE_CORE_UINT256_PATTERNS_PASS: case uint256(p) through the public API, every uint256 value matching uint256(w) with w its word, a literal, a wildcard and a group inside, two inside a tuple, an open scrutinee taking uint256, and uint8(w) and int256(w), uint256(w) at Word and uint8, and two patterns inside rejected"

/-- The boolean literal pattern: `true` and `false` in a pattern name the booleans, as they do
in an expression, as upstream reads them. `flag` and `pair` are the match probes `m4` and `m8`
with a catch-all after them, as `m4c` and `m8c` measure them on upstream's driver. -/
private def boolPatternWorkspace : Workspace.RawWorkspace := workspaceOf [
  "enum Pair<a> { Pair(Bool, a) }",
  "function flag(a: Bool) returns (Word) { match (a) { case true { return 1; } case false { return 2; } case _ { return 3; } } }",
  "function pair(p: Pair<Word>) returns (Word) { match (p) { case Pair.Pair(true, x) { return 1; } case Pair.Pair(false, x) { return 2; } case _ { return 3; } } }",
  "function pairTrue() returns (Word) { return pair(Pair.Pair(true, 5)); }",
  "function pairFalse() returns (Word) { return pair(Pair.Pair(false, 5)); }",
  "function both(a: Bool, b: Bool) returns (Word) { match (a, b) { case (true, true) { return 1; } case (false, y) { return 2; } case (_, _) { return 3; } } }",
  "function grouped(a: Bool) returns (Word) { match (a) { case (false) { return 4; } case _ { return 5; } } }",
  "function bound() returns (Word) { let x = false; match (x) { case false { return 6; } case _ { return 7; } } }"]

private def boolPatternNames : List String :=
  ["flag", "pairTrue", "pairFalse", "both", "grouped", "bound"]

/-- The boolean literal pattern through the public API: each arm runs for its own boolean, a
repeated `true` binds nothing, and a group and a `let`-bound scrutinee take `bool`. A match on `bool`
with no catch-all, `m4`, and one that splits a payload's boolean, `m8`, run in the coverage
test; `m9`, which upstream refuses, and upstream's `typeck/tuple_nested_nonexhaustive` are
refused, and `true` at `Word` is a type error. -/
def runBoolPatterns : IO Unit := do
  let program ← get "bool pattern check" (checkProgram boolPatternWorkspace)
  let seeds ← boolPatternNames.mapM (seed program)
  let compiled ← get "bool pattern compilation"
    (compile boolPatternWorkspace seeds {specializationBudget := 256, compilationFuel := 1000})
  let key (name : String) : IO Key := match boolPatternNames.findIdx? (· == name) with
    | some index => match compiled.keys[index]? with
      | some key => pure key
      | none => throw (IO.userError s!"bool pattern root {name} missing")
    | none => throw (IO.userError s!"bool pattern {name} unknown")
  let mut session ← boot (← compiled.open)
  let cases : List (String × List Value × Value) := [
    ("flag", [boolean true], word 1), ("flag", [boolean false], word 2),
    ("pairTrue", [], word 1), ("pairFalse", [], word 2),
    ("both", [boolean true, boolean true], word 1), ("both", [boolean false, boolean true], word 2),
    ("both", [boolean true, boolean false], word 3),
    ("grouped", [boolean false], word 4), ("grouped", [boolean true], word 5),
    ("bound", [], word 6)]
  for (name, arguments, expected) in cases do
    let completed ← execute session (← key name) arguments
    require (completed.value == expected) s!"{name} on {reprStr arguments} gave {reprStr completed.value}"
    session := completed.session
  let _ := session
  -- Upstream refuses these two (`SC0302`).
  rejectedByInference "m9, a payload's false missing"
    ["enum Pair<a> { Pair(Bool, a) }",
      "function pair(p: Pair<Word>) returns (Word) { match (p) { case Pair.Pair(true, x) { return x; } } }"]
  rejectedByInference "tuple_nested_nonexhaustive"
    ["function nested(p: ((), (Bool, Word))) returns (Word) { match (p) { case ((), (true, x)) { return x; } } }"]
  rejectedByInference "true at Word"
    ["function bad(x: Word) returns (Word) { match (x) { case true { return 1; } case _ { return 0; } } }"]
  IO.println "SOURCE_CORE_BOOL_PATTERNS_PASS: case true and case false through the public API, each arm for its own boolean in a bool match and in a payload as the m4c and m8c probes give upstream's 2, a repeated true in a tuple binding nothing, a group and a let-bound scrutinee taking bool; m9 and tuple_nested_nonexhaustive refused as upstream refuses them, and true at Word rejected"

/-- Upstream's reading of a bare name in a pattern, after `true` and `false`: a constructor that
shares its type's name is that constructor, as `same-name-ctor-pattern` measures it; any other
visible constructor of that spelling is refused, as upstream's `SC0106` refuses it, whatever the
scrutinee's type; and any other name is a binder. -/
private def bareNameWorkspace : Workspace.RawWorkspace := workspaceOf [
  "enum m { m, k }",
  "enum thing { thing }",
  "enum colour { red, blue }",
  "function pickM(x: m) returns (Word) { match (x) { case m { return 1; } case m.k { return 2; } } }",
  "function pickThing(t: thing) returns (Word) { match (t) { case thing { return 7; } } }",
  "function colourBinder(c: colour) returns (Word) { match (c) { case colour { return 3; } } }",
  "function first() returns (Word) { return pickM(m.m); }",
  "function second() returns (Word) { return pickM(m.k); }",
  "function only() returns (Word) { return pickThing(thing.thing); }",
  "function blue() returns (Word) { return colourBinder(colour.blue); }"]

private def bareNameNames : List String := ["first", "second", "only", "blue"]

/-- A main module and a module `lib` beside it. -/
private def libraryWorkspace (main library : String) : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content := "pragma solcore;\n" ++ main},
    {path := "lib.solc", content := "pragma solcore;\n" ++ library}] }

/-- Inference refuses the program with exactly this error. -/
private def refusedWith (label : String) (workspace : Workspace.RawWorkspace)
    (error : Frontend.SourceInference.Error) : IO Unit :=
  match checkProgram workspace with
  | .ok _ => throw (IO.userError s!"{label} was accepted")
  | .error [.inference failure] =>
      if failure.error == error then pure ()
      else throw (IO.userError s!"{label} gave {reprStr failure.error}")
  | .error errors => throw (IO.userError s!"{label} gave {reprStr errors}")

private def flagLibrary : String := "export { flag(*) };\nenum flag { on, off }"

private def pickFlag (type : String) (qualified : String) : String :=
  s!"function pick(f: {type}) returns (Word) \{ match (f) \{ case off \{ return 1; } case {qualified} \{ return 2; } } }"

/-- The bare-name rule through the public API: same-name constructors run as their constructors,
`case m` beside `case m.k` covering `m`; a type's name with no constructor of that name, and a
constructor an import keeps opaque, stay binders; and a visible constructor's spelling is refused
as a binder, at its own scrutinee, at an unrelated one, nested, beside a parameter of that name,
and through a selected, wildcard or plain import, as the pinned checker refuses each one. -/
def runBareNamePatterns : IO Unit := do
  let program ← get "bare name check" (checkProgram bareNameWorkspace)
  let seeds ← bareNameNames.mapM (seed program)
  let compiled ← get "bare name compilation"
    (compile bareNameWorkspace seeds {specializationBudget := 256, compilationFuel := 1000})
  let key (name : String) : IO Key := match bareNameNames.findIdx? (· == name) with
    | some index => match compiled.keys[index]? with
      | some key => pure key
      | none => throw (IO.userError s!"bare name root {name} missing")
    | none => throw (IO.userError s!"bare name {name} unknown")
  let mut session ← boot (← compiled.open)
  let cases : List (String × List Value × Value) := [
    ("first", [], word 1), ("second", [], word 2), ("only", [], word 7), ("blue", [], word 3)]
  for (name, arguments, expected) in cases do
    let completed ← execute session (← key name) arguments
    require (completed.value == expected) s!"{name} on {reprStr arguments} gave {reprStr completed.value}"
    session := completed.session
  let _ := session
  -- An opaque import's constructors are not visible, so `off` binds.
  match checkProgram (libraryWorkspace
      "import { flag, makeOn } from lib;\nfunction pick(f: flag) returns (Word) { match (f) { case off { return 1; } } }"
      "export { flag, makeOn };\nenum flag { on, off }\nfunction makeOn() returns (flag) { return flag.on; }") with
  | .ok _ => pure ()
  | .error errors => throw (IO.userError s!"an opaque import's constructor spelling gave {reprStr errors}")
  -- Upstream's `nameres/unqualified_ctor_pattern`, refused at `off`.
  refusedWith "unqualified_ctor_pattern" (workspaceOf ["enum flag { off, on }",
    "function pick(f: flag) returns (Word) { match (f) { case off { return 0; } case on { return 1; } } }",
    "function main() returns (Word) { return pick(flag.on); }"]) (.unqualifiedConstructorPattern "off")
  refusedWith "a binder spelled like an unrelated type's constructor" (workspaceOf ["enum flag { on, off }",
    "function f(x: Word) returns (Word) { match (x) { case on { return 1; } } }"])
    (.unqualifiedConstructorPattern "on")
  refusedWith "a nested binder spelled like another type's constructor" (workspaceOf ["enum flag { on, off }",
    "enum Box { Box(Word) }", "function f(b: Box) returns (Word) { match (b) { case Box.Box(off) { return off; } } }"])
    (.unqualifiedConstructorPattern "off")
  refusedWith "a binder spelled like a constructor beside a parameter of that name" (workspaceOf ["enum flag { on, off }",
    "function pick(off: Word, f: flag) returns (Word) { match (f) { case off { return 1; } case flag.on { return 2; } } }"])
    (.unqualifiedConstructorPattern "off")
  refusedWith "a selected import's constructor" (libraryWorkspace
    ("import { flag } from lib;\n" ++ pickFlag "flag" "flag.on") flagLibrary) (.unqualifiedConstructorPattern "off")
  refusedWith "a wildcard import's constructor" (libraryWorkspace
    ("import * from lib;\n" ++ pickFlag "flag" "flag.on") flagLibrary) (.unqualifiedConstructorPattern "off")
  refusedWith "a plain import's constructor" (libraryWorkspace
    ("import lib;\n" ++ pickFlag "lib.flag" "lib.flag.on") flagLibrary) (.unqualifiedConstructorPattern "off")
  -- A same-name constructor with a payload, written bare, is that constructor, short of its argument.
  rejectedByInference "a bare same-name constructor with a payload"
    ["enum box { box(Word) }", "function f(b: box) returns (Word) { match (b) { case box { return 1; } } }"]
  IO.println "SOURCE_CORE_BARE_NAME_PATTERNS_PASS: a bare name in a pattern as upstream reads it through the public API, same-name constructors m and thing running as their constructors with case m beside case m.k covering m, a type name with no constructor of that name and an opaque import's constructor binding, and a visible constructor's spelling refused as upstream's SC0106 refuses it, upstream's unqualified_ctor_pattern, at an unrelated scrutinee, nested, beside a parameter of that name and through a selected, wildcard and plain import, and a bare same-name constructor with a payload refused for its argument"

private def constructorNamesWorkspace : Workspace.RawWorkspace := workspaceOf [
  "enum Option { None, Some(Word) }",
  "enum Box { Box(Word) }",
  "enum E { inl(Word), other }",
  "enum thing { thing }",
  "enum Flag { Flag }",
  "enum Tag<a> { Tag }",
  "enum Cell<a> { Cell(a) }",
  "enum Holder { Holder(thing, Word) }",
  "enum tag { tag }",
  "function unbox(b: Box) returns (Word) { match (b) { case Box(w) { return w; } } }",
  "function getE(e: E) returns (Word) { match (e) { case inl(x) { return x; } case E.other { return 0; } } }",
  "function getOption(o: Option) returns (Word) { match (o) { case .None { return 0; } case .Some(v) { return v; } } }",
  "function pickThing(t: thing) returns (Word) { match (t) { case thing.thing { return 7; } } }",
  "function pickFlag(f: Flag) returns (Word) { match (f) { case Flag { return 8; } } }",
  "function tagged(t: Tag<Word>, c: Cell<Word>) returns (Word) { match (c) { case Cell.Cell(v) { return v; } } }",
  "function count(h: Holder) returns (Word) { match (h) { case Holder.Holder(t, w) { return w; } } }",
  "function make() returns (thing) { return thing; }",
  "function tag() returns (Word) { return 3; }",
  "function boxed(w: Word) returns (Word) { return unbox(Box(w)); }",
  "function inlined(w: Word) returns (Word) { return getE(E.inl(w)); }",
  "function optional(w: Word) returns (Word) { return getOption(Option.Some(w)); }",
  "function bare() returns (Word) { return pickThing(thing); }",
  "function made() returns (Word) { return pickThing(make()); }",
  "function capital() returns (Word) { return pickFlag(Flag); }",
  "function generic(w: Word) returns (Word) { return tagged(Tag, Cell(w)); }",
  "function held(w: Word) returns (Word) { return count(Holder(thing, w)); }",
  "function shadowed() returns (Word) { let thing: Word = 5; return thing; }",
  "function parameter(thing: Word) returns (Word) { return thing; }",
  "function viaFunction() returns (Word) { let f = tag; return f(); }"]

private def constructorNamesNames : List String :=
  ["boxed", "inlined", "optional", "bare", "made", "capital", "generic", "held", "shadowed", "parameter",
    "viaFunction"]

private def thingLibrary : String := "export { thing(*) };\nenum thing { thing }"

private def pickThingIn (type : String) : String :=
  s!"function pick(t: {type}) returns (Word) \{ match (t) \{ case _ \{ return 7; } } }\nfunction main() returns (Word) \{ return pick(thing); }"

/-- Constructor names as upstream reads them, through the public API. In a pattern, an unqualified
head that shares its type's name is that type's constructor, a head spelled like one of upstream's
builtin constructors (`inl`) is left to the scrutinee's type, and a leading dot is unchanged; any
other unqualified head that spells a visible constructor is refused, as upstream's `SC0106` refuses
it. In an expression, a bare name that no local, parameter or function takes and that names a
constructor sharing its type's name is that constructor applied to no payload, in the module and
through a selected or wildcard import; through a plain or opaque import, or for any other
constructor, the name stays unknown. -/
def runConstructorNames : IO Unit := do
  let program ← get "constructor names check" (checkProgram constructorNamesWorkspace)
  let seeds ← constructorNamesNames.mapM (seed program)
  let compiled ← get "constructor names compilation"
    (compile constructorNamesWorkspace seeds {specializationBudget := 256, compilationFuel := 1000})
  let key (name : String) : IO Key := match constructorNamesNames.findIdx? (· == name) with
    | some index => match compiled.keys[index]? with
      | some key => pure key
      | none => throw (IO.userError s!"constructor names root {name} missing")
    | none => throw (IO.userError s!"constructor names {name} unknown")
  let mut session ← boot (← compiled.open)
  let cases : List (String × List Value × Value) := [
    ("boxed", [word 5], word 5), ("inlined", [word 9], word 9), ("optional", [word 4], word 4),
    ("bare", [], word 7), ("made", [], word 7), ("capital", [], word 8), ("generic", [word 3], word 3),
    ("held", [word 2], word 2), ("shadowed", [], word 5), ("parameter", [word 6], word 6),
    ("viaFunction", [], word 3)]
  for (name, arguments, expected) in cases do
    let completed ← execute session (← key name) arguments
    require (completed.value == expected) s!"{name} on {reprStr arguments} gave {reprStr completed.value}"
    session := completed.session
  let _ := session
  -- A bare same-name constructor through a selected or wildcard import.
  for (label, main) in [("a selected import", "import { thing } from lib;\n"), ("a wildcard import", "import * from lib;\n")] do
    match checkProgram (libraryWorkspace (main ++ pickThingIn "thing") thingLibrary) with
    | .ok _ => pure ()
    | .error errors => throw (IO.userError s!"a bare constructor through {label} gave {reprStr errors}")
  -- Unqualified heads upstream refuses with `SC0106`.
  refusedWith "an unqualified head" (workspaceOf ["enum Option { None, Some(Word) }",
    "function get(o: Option) returns (Word) { match (o) { case None { return 0; } case Option.Some(v) { return v; } } }"])
    (.unqualifiedConstructorPattern "None")
  refusedWith "an unqualified head with a payload" (workspaceOf ["enum Option { None, Some(Word) }",
    "function get(o: Option) returns (Word) { match (o) { case Some(v) { return v; } case Option.None { return 0; } } }"])
    (.unqualifiedConstructorPattern "Some")
  refusedWith "an unqualified head through a selected import" (libraryWorkspace
    "import { Option } from lib;\nfunction get(o: Option) returns (Word) { match (o) { case Some(v) { return v; } case Option.None { return 0; } } }"
    "export { Option(*) };\nenum Option { None, Some(Word) }") (.unqualifiedConstructorPattern "Some")
  refusedWith "an unqualified head through a plain import" (libraryWorkspace
    "import lib;\nfunction get(o: lib.Option) returns (Word) { match (o) { case None { return 0; } case lib.Option.Some(v) { return v; } } }"
    "export { Option(*) };\nenum Option { None, Some(Word) }") (.unqualifiedConstructorPattern "None")
  -- A same-name head is that type's constructor, so it does not match a scrutinee of another type.
  rejectedByInference "a same-name head at another type"
    ["enum Box { Box(Word) }", "enum Wrapper { Box(Word), Empty }",
      "function f(w: Wrapper) returns (Word) { match (w) { case Box(v) { return v; } case Wrapper.Empty { return 0; } } }"]
  -- Bare names upstream does not read as constructors stay unknown.
  refusedWith "a bare constructor of another name" (workspaceOf ["enum flag { on, off }",
    "function main() returns (Word) { let f: flag = on; return 1; }"]) (.unknownVariable "on")
  refusedWith "a bare capitalized constructor of another name" (workspaceOf ["enum Option { None, Some(Word) }",
    "function main() returns (Word) { let o: Option = None; return 1; }"]) (.unknownVariable "None")
  refusedWith "a bare same-name constructor through a plain import" (libraryWorkspace
    "import lib;\nfunction main() returns (Word) { let t: lib.thing = thing; return 1; }" thingLibrary)
    (.unknownVariable "thing")
  refusedWith "a bare same-name constructor through an opaque import" (libraryWorkspace
    "import { thing, make } from lib;\nfunction main() returns (Word) { let t: thing = thing; return 1; }"
    "export { thing, make };\nenum thing { thing }\nfunction make() returns (thing) { return thing.thing; }")
    (.unknownVariable "thing")
  -- A same-name constructor with a payload, written bare, is that constructor, short of its payload.
  rejectedByInference "a bare same-name constructor with a payload"
    ["enum Box { Box(Word) }", "function main() returns (Word) { let make = Box; return 1; }"]
  IO.println "SOURCE_CORE_CONSTRUCTOR_NAMES_PASS: constructor names as upstream reads them through the public API, an unqualified same-name head running as its type's constructor, a head spelled like upstream's builtin inl left to the scrutinee's type and leading dots unchanged, any other unqualified head refused as upstream's SC0106 refuses it, in the module and through a selected and a plain import, a same-name head refused at another type, and a bare same-name constructor running as that constructor with no payload, as a value, an argument, a payload and a generic, through a selected and a wildcard import, under a local, a parameter and a function of that name, and unknown through a plain or an opaque import, for another constructor's name or with a payload"

/-- Upstream's coverage, as `MatchExhaustive.covered` states it: the arms cover the scrutinee's
type with no catch-all. `flag` and `pair` are the probes `m4` and `m8`, `held` is `x19`'s nested
same-name constructor, `both` the boolean matrix of `c3`, `firstOf` the parenthesized tuple of
`c4`, `unwrap` the payload split of `c5`, `wordOrFlag` a `uint256(w)` beside a boolean, and `just`
a generic payload at `Bool`. -/
private def coverageWorkspace : Workspace.RawWorkspace := workspaceOf [
  "enum Pair<a> { Pair(Bool, a) }",
  "enum thing { thing }",
  "enum Holder { Holder(thing, Word) }",
  "enum Opt { None, Some(Word) }",
  "enum Wrap { Wrap(Opt) }",
  "enum Maybe<a> { Nothing, Just(a) }",
  "function flag(a: Bool) returns (Word) { match (a) { case true { return 1; } case false { return 2; } } }",
  "function pair(p: Pair<Word>) returns (Word) { match (p) { case Pair.Pair(true, x) { return x; } case Pair.Pair(false, x) { return 9; } } }",
  "function held(h: Holder) returns (Word) { match (h) { case Holder.Holder(thing.thing, w) { return w; } } }",
  "function both(a: Bool, b: Bool) returns (Word) { match (a, b) { case (true, true) { return 1; } case (true, false) { return 2; } case (false, _) { return 3; } } }",
  "function firstOf(p: (Word, Word)) returns (Word) { match (p) { case ((head, _)) { return head; } } }",
  "function unwrap(w: Wrap) returns (Word) { match (w) { case Wrap.Wrap(Opt.None) { return 0; } case Wrap.Wrap(Opt.Some(v)) { return v; } } }",
  "function wordOrFlag(x: uint256, b: Bool) returns (Word) { match (x, b) { case (uint256(w), true) { return w; } case (_, false) { return 5; } } }",
  "function just(m: Maybe<Bool>) returns (Word) { match (m) { case Maybe.Just(true) { return 1; } case Maybe.Just(false) { return 2; } case Maybe.Nothing { return 3; } } }",
  "function pairTrue() returns (Word) { return pair(Pair.Pair(true, 6)); }",
  "function pairFalse() returns (Word) { return pair(Pair.Pair(false, 6)); }",
  "function heldTwo() returns (Word) { return held(Holder.Holder(thing.thing, 2)); }",
  "function firstPair() returns (Word) { return firstOf((7, 8)); }",
  "function unwrapNone() returns (Word) { return unwrap(Wrap.Wrap(Opt.None)); }",
  "function unwrapSome() returns (Word) { return unwrap(Wrap.Wrap(Opt.Some(4))); }",
  "function justTrue() returns (Word) { return just(Maybe.Just(true)); }",
  "function justFalse() returns (Word) { return just(Maybe.Just(false)); }",
  "function nothing() returns (Word) { let m: Maybe<Bool> = Maybe.Nothing; return just(m); }"]

private def coverageNames : List String :=
  ["flag", "both", "wordOrFlag", "pairTrue", "pairFalse", "heldTwo", "firstPair", "unwrapNone",
    "unwrapSome", "justTrue", "justFalse", "nothing"]

/-- Inference refuses the program as a match that its arms do not cover. -/
private def refusedNonExhaustive (label : String) (workspace : Workspace.RawWorkspace) : IO Unit :=
  match checkProgram workspace with
  | .ok _ => throw (IO.userError s!"{label} was accepted")
  | .error [.inference failure] =>
      if failure.error matches .nonExhaustiveMatch _ then pure ()
      else throw (IO.userError s!"{label} gave {reprStr failure.error}")
  | .error errors => throw (IO.userError s!"{label} gave {reprStr errors}")

private def partialFlagLibrary : String :=
  "export { flag(on), makeOff };\nenum flag { on, off }\nfunction makeOff() returns (flag) { return flag.off; }"

/-- Upstream's coverage through the public API: matches that only their arms together cover run each
arm, and the ones upstream refuses as not covered (`SC0302`) or for a hidden constructor with no
catch-all at its column (`SC0223`) are refused, a hidden column covered through another column
accepted. -/
def runMatchCoverage : IO Unit := do
  let program ← get "coverage check" (checkProgram coverageWorkspace)
  let seeds ← coverageNames.mapM (seed program)
  let compiled ← get "coverage compilation"
    (compile coverageWorkspace seeds {specializationBudget := 256, compilationFuel := 1000})
  let key (name : String) : IO Key := match coverageNames.findIdx? (· == name) with
    | some index => match compiled.keys[index]? with
      | some key => pure key
      | none => throw (IO.userError s!"coverage root {name} missing")
    | none => throw (IO.userError s!"coverage {name} unknown")
  let mut session ← boot (← compiled.open)
  let cases : List (String × List Value × Value) := [
    ("flag", [boolean true], word 1), ("flag", [boolean false], word 2),
    ("both", [boolean true, boolean true], word 1), ("both", [boolean true, boolean false], word 2),
    ("both", [boolean false, boolean true], word 3),
    ("wordOrFlag", [word 3, boolean true], word 3), ("wordOrFlag", [word 3, boolean false], word 5),
    ("pairTrue", [], word 6), ("pairFalse", [], word 9), ("heldTwo", [], word 2),
    ("firstPair", [], word 7), ("unwrapNone", [], word 0), ("unwrapSome", [], word 4),
    ("justTrue", [], word 1), ("justFalse", [], word 2), ("nothing", [], word 3)]
  for (name, arguments, expected) in cases do
    let completed ← execute session (← key name) arguments
    require (completed.value == expected) s!"{name} on {reprStr arguments} gave {reprStr completed.value}"
    session := completed.session
  let _ := session
  -- A column with a hidden constructor, covered through the other column (`h6`).
  match checkProgram (libraryWorkspace
      "import { flag, makeOff } from lib;\nfunction pick(f: flag, b: Bool) returns (Word) { match (f, b) { case (flag.on, _) { return 1; } case (_, true) { return 2; } case (_, false) { return 3; } } }"
      partialFlagLibrary) with
  | .ok _ => pure ()
  | .error errors => throw (IO.userError s!"a hidden column covered through another gave {reprStr errors}")
  -- Upstream refuses these (`SC0302`).
  refusedNonExhaustive "a boolean pair missing (false, true)" (workspaceOf [
    "function pick(a: Bool, b: Bool) returns (Word) { match (a, b) { case (true, true) { return 1; } case (true, false) { return 2; } case (false, false) { return 3; } } }"])
  refusedNonExhaustive "a payload's Some missing" (workspaceOf ["enum Opt { None, Some(Word) }",
    "enum Wrap { Wrap(Opt) }",
    "function get(w: Wrap) returns (Word) { match (w) { case Wrap.Wrap(Opt.None) { return 0; } } }"])
  refusedNonExhaustive "word literals with no catch-all" (workspaceOf [
    "function f(w: Word) returns (Word) { match (w) { case 0 { return 1; } case 1 { return 2; } } }"])
  refusedNonExhaustive "a generic payload's false missing" (workspaceOf ["enum Maybe<a> { Nothing, Just(a) }",
    "function f(m: Maybe<Bool>) returns (Word) { match (m) { case Maybe.Just(true) { return 1; } case Maybe.Nothing { return 3; } } }"])
  refusedNonExhaustive "a uint256 beside a boolean missing (_, false)" (workspaceOf [
    "function f(x: uint256, b: Bool) returns (Word) { match (x, b) { case (uint256(w), true) { return w; } } }"])
  -- Upstream refuses these for the hidden constructor (`SC0223`).
  refusedNonExhaustive "a hidden constructor's type, its visible one only" (libraryWorkspace
    "import { flag, makeOff } from lib;\nfunction pick(f: flag) returns (Word) { match (f) { case flag.on { return 1; } } }"
    partialFlagLibrary)
  refusedNonExhaustive "a hidden column with no catch-all" (libraryWorkspace
    "import { flag, makeOff } from lib;\nfunction pick(f: flag, b: Bool) returns (Word) { match (f, b) { case (flag.on, _) { return 1; } } }"
    partialFlagLibrary)
  IO.println "SOURCE_CORE_MATCH_COVERAGE_PASS: upstream's coverage through the public API, matches that only their arms together cover running each arm, a bool match and a payload's boolean split (m4, m8), a nested same-name constructor (x19), a boolean matrix, a parenthesized tuple, a payload split over its constructors, a uint256 word beside a boolean and a generic payload at Bool, a hidden column covered through another accepted, and refused as upstream refuses them: a missing boolean pair, a payload's missing constructor, word literals, a generic payload's missing false, a uint256 column's missing boolean, and a hidden constructor's type with no catch-all at its column"

/-- A call of a name that a declared function or a builtin takes, beside a constructor that shares
its type's name, as upstream reads it (`f1` to `f10`): the function or the builtin is called, and
the qualified constructor stays the constructor, as does a same-name constructor with no function
of its name. -/
private def callLookupWorkspace : Workspace.RawWorkspace := workspaceOf [
  "enum thing { thing }",
  "enum Box { Box(Word) }",
  "enum Cell<a> { Cell(a) }",
  "enum Only { Only(Word) }",
  "enum primAddWord { primAddWord(Word, Word) }",
  "function thing() returns (Word) { return 3; }",
  "function Box(w: Word) returns (Word) { return 7; }",
  "function Cell(x: Word) returns (Word) { return 9; }",
  "function unbox(b: Box) returns (Word) { match (b) { case Box.Box(v) { return v; } } }",
  "function unonly(o: Only) returns (Word) { match (o) { case Only(v) { return v; } } }",
  "function nullary() returns (Word) { return thing(); }",
  "function payload(w: Word) returns (Word) { return Box(w); }",
  "function generic(w: Word) returns (Word) { return Cell(w); }",
  "function qualified(w: Word) returns (Word) { return unbox(Box.Box(w)); }",
  "function constructed(w: Word) returns (Word) { return unonly(Only(w)); }",
  "function builtin(a: Word, b: Word) returns (Word) { return primAddWord(a, b); }"]

private def callLookupNames : List String :=
  ["nullary", "payload", "generic", "qualified", "constructed", "builtin"]

/-- Inference refuses the program because the function a call names does not take its
arguments. -/
private def refusedAsFunctionCall (label : String) (workspace : Workspace.RawWorkspace)
    (name : String) : IO Unit :=
  match checkProgram workspace with
  | .ok _ => throw (IO.userError s!"{label} was accepted")
  | .error [.inference failure] =>
      match failure.error with
      | .noMatchingOverload actual _ =>
          if actual == name then pure ()
          else throw (IO.userError s!"{label} gave {reprStr failure.error}")
      | _ => throw (IO.userError s!"{label} gave {reprStr failure.error}")
  | .error errors => throw (IO.userError s!"{label} gave {reprStr errors}")

private def boxFunctionLibrary : String :=
  "export { Box };\nfunction Box(w: Word) returns (Word) { return 7; }"

/-- The call rule through the public API: a declared function, local or imported, or a builtin
takes an unqualified call before a constructor that shares its type's name, as a bare name in an
expression reads it; a function that does not take the call's arguments refuses it, as upstream's
`SC0203` and `SC0201` do, rather than leaving it to the constructor. -/
def runCallLookup : IO Unit := do
  let program ← get "call lookup check" (checkProgram callLookupWorkspace)
  let seeds ← callLookupNames.mapM (seed program)
  let compiled ← get "call lookup compilation"
    (compile callLookupWorkspace seeds {specializationBudget := 256, compilationFuel := 1000})
  let key (name : String) : IO Key := match callLookupNames.findIdx? (· == name) with
    | some index => match compiled.keys[index]? with
      | some key => pure key
      | none => throw (IO.userError s!"call lookup root {name} missing")
    | none => throw (IO.userError s!"call lookup {name} unknown")
  let mut session ← boot (← compiled.open)
  let cases : List (String × List Value × Value) := [
    ("nullary", [], word 3), ("payload", [word 5], word 7), ("generic", [word 5], word 9),
    ("qualified", [word 5], word 5), ("constructed", [word 4], word 4),
    ("builtin", [word 1, word 2], word 3)]
  for (name, arguments, expected) in cases do
    let completed ← execute session (← key name) arguments
    require (completed.value == expected) s!"{name} on {reprStr arguments} gave {reprStr completed.value}"
    session := completed.session
  let _ := session
  -- The function imported and the constructor local, the other way round, and both imported.
  for (label, main, library) in [
      ("an imported function",
        "import { Box } from lib;\nenum Box { Box(Word) }\nfunction main() returns (Word) { let w: Word = 5; return Box(w); }",
        boxFunctionLibrary),
      ("an imported constructor",
        "import { Box } from lib;\nfunction Box(w: Word) returns (Word) { return 7; }\nfunction main() returns (Word) { let w: Word = 5; return Box(w); }",
        "export { Box(*) };\nenum Box { Box(Word) }"),
      ("both through a wildcard import",
        "import * from lib;\nfunction main() returns (Word) { let w: Word = 5; return Box(w); }",
        "export { Box(*), Box };\nenum Box { Box(Word) }\nfunction Box(w: Word) returns (Word) { return 7; }")] do
    match checkProgram (libraryWorkspace main library) with
    | .ok _ => pure ()
    | .error errors => throw (IO.userError s!"a function beside a constructor, {label}, gave {reprStr errors}")
  -- A function that does not take the arguments refuses the call (`SC0203`, `SC0201`).
  refusedAsFunctionCall "a function of no argument called with one" (workspaceOf ["enum Box { Box(Word) }",
    "function Box() returns (Word) { return 7; }",
    "function main() returns (Word) { let w: Word = 5; return Box(w); }"]) "Box"
  refusedAsFunctionCall "a function of a Bool called with a Word" (workspaceOf ["enum Box { Box(Word) }",
    "function Box(b: Bool) returns (Word) { return 7; }",
    "function main() returns (Word) { let w: Word = 5; return Box(w); }"]) "Box"
  IO.println "SOURCE_CORE_CALL_LOOKUP_PASS: a call of a name that a declared function or a builtin takes through the public API, the function called before a constructor that shares its type's name with no payload, with a payload and generic, the builtin primAddWord before a same-name constructor, the qualified constructor and a same-name constructor with no function of its name still constructors, an imported function before a local constructor, a local function before an imported one and both through a wildcard import, and a function that does not take the arguments refusing the call as upstream's SC0203 and SC0201 do"

/-- `.true` and `.false` where an expected `bool` reaches them, as upstream reads a leading dot at
a builtin type: a condition, a loop's condition, an annotated `let`, a result, an assignment, a
conditional's condition and `()` after the name. -/
private def leadingDotBooleanWorkspace : Workspace.RawWorkspace := workspaceOf [
  "function pick(b: Bool) returns (Word) { if (b) { return 1; } return 2; }",
  "function yes() returns (Bool) { return .true; }",
  "function condition() returns (Word) { if (.true) { return 1; } return 2; }",
  "function loops() returns (Word) { let n: Word = 4; while (.false) { n = 1; } for (let i: Word = 0; .false; i = 1) { n = 2; } return n; }",
  "function annotated() returns (Word) { let b: Bool = .false; return pick(b); }",
  "function returned() returns (Word) { return pick(yes()); }",
  "function assigned() returns (Word) { let b: Bool = true; b = .false; return pick(b); }",
  "function chosen() returns (Word) { return .true ? 1 : 2; }",
  "function called() returns (Word) { let b: Bool = .true(); return pick(b); }"]

private def leadingDotBooleanNames : List String :=
  ["condition", "loops", "annotated", "returned", "assigned", "chosen", "called"]

/-- Inference refuses the program at a leading-dot `true` or `false` that no expected `bool`
reaches. -/
private def refusedLeadingDotBoolean (label : String) (lines : List String) : IO Unit :=
  match checkProgram (workspaceOf lines) with
  | .ok _ => throw (IO.userError s!"{label} was accepted")
  | .error [.inference failure] =>
      match failure.error with
      | .constructorNeedsExpectedType name =>
          if name == "true" || name == "false" then pure ()
          else throw (IO.userError s!"{label} gave {reprStr failure.error}")
      | _ => throw (IO.userError s!"{label} gave {reprStr failure.error}")
  | .error errors => throw (IO.userError s!"{label} gave {reprStr errors}")

/-- Leading-dot booleans through the public API: where an expected `bool` reaches `.true` or
`.false`, they are the booleans; with no expected type, at another type, at a generic parameter, as
an operand of `==` or `!`, or with an argument, they are refused, as upstream refuses them
(`SC0224`). -/
def runLeadingDotBooleans : IO Unit := do
  let program ← get "leading-dot boolean check" (checkProgram leadingDotBooleanWorkspace)
  let seeds ← leadingDotBooleanNames.mapM (seed program)
  let compiled ← get "leading-dot boolean compilation"
    (compile leadingDotBooleanWorkspace seeds {specializationBudget := 256, compilationFuel := 1000})
  let key (name : String) : IO Key := match leadingDotBooleanNames.findIdx? (· == name) with
    | some index => match compiled.keys[index]? with
      | some key => pure key
      | none => throw (IO.userError s!"leading-dot boolean root {name} missing")
    | none => throw (IO.userError s!"leading-dot boolean {name} unknown")
  let mut session ← boot (← compiled.open)
  let cases : List (String × Value) := [
    ("condition", word 1), ("loops", word 4), ("annotated", word 2), ("returned", word 1),
    ("assigned", word 2), ("chosen", word 1), ("called", word 1)]
  for (name, expected) in cases do
    let completed ← execute session (← key name) []
    require (completed.value == expected) s!"{name} gave {reprStr completed.value}"
    session := completed.session
  let _ := session
  refusedLeadingDotBoolean "no expected type"
    ["function bad() returns (Word) { let b = .true; return 1; }"]
  refusedLeadingDotBoolean "an expected Word"
    ["function bad() returns (Word) { let w: Word = .true; return 1; }"]
  refusedLeadingDotBoolean "a generic parameter"
    ["function h<T>(x: T) returns (T) { return x; }",
      "function bad() returns (Word) { h(.true); return 1; }"]
  refusedLeadingDotBoolean "an operand of =="
    ["function bad(x: Bool) returns (Word) { if (.true == x) { return 1; } return 2; }"]
  refusedLeadingDotBoolean "an operand of !"
    ["function bad() returns (Word) { if (!.false) { return 1; } return 2; }"]
  refusedLeadingDotBoolean "with an argument"
    ["function bad() returns (Word) { let b: Bool = .true(1); return 1; }"]
  IO.println "SOURCE_CORE_LEADING_DOT_BOOLEANS_PASS: .true and .false through the public API, the booleans where an expected bool reaches them (a condition, a loop's condition, an annotated let, a result, an assignment, a conditional's condition and () after the name), and refused with no expected type, at Word, at a generic parameter, as an operand of == or ! and with an argument, as upstream refuses them (SC0224)"

/-- A block that ends in a `return`, with statements after it, and a `return` last in its branch:
both accepted, as upstream accepts them, and the block returns early. -/
private def nonFinalReturnWorkspace : Workspace.RawWorkspace := workspaceOf [
  "function blockEarly() returns (Word) { let x: Word = 0; { return 1; } x = 2; return x; }",
  "function lastInBranch() returns (Word) { if (true) { return 1; } return 2; }"]

private def nonFinalReturnNames : List String := ["blockEarly", "lastInBranch"]

/-- Checking refuses the program at a `return` that another statement of its sequence follows. -/
private def refusedNonFinalReturn (label : String) (lines : List String) : IO Unit :=
  match checkProgram (workspaceOf lines) with
  | .ok _ => throw (IO.userError s!"{label} was accepted")
  | .error [.inference failure] =>
      match failure.error with
      | .nonFinalReturn _ => pure ()
      | _ => throw (IO.userError s!"{label} gave {reprStr failure.error}")
  | .error [.methodInference _ (.nonFinalReturn _)] => pure ()
  | .error errors => throw (IO.userError s!"{label} gave {reprStr errors}")

/-- Upstream's `SC0222` through the public API: a `return` that another statement of its sequence
follows is refused in every sequence, a body's, a block's, a branch's, a loop's, a match arm's, a
lambda's and an implementation method's, whether or not anything calls it; a block that ends in a
`return` is accepted with statements after it, and returns early. -/
def runNonFinalReturns : IO Unit := do
  let program ← get "non-final return check" (checkProgram nonFinalReturnWorkspace)
  let seeds ← nonFinalReturnNames.mapM (seed program)
  let compiled ← get "non-final return compilation"
    (compile nonFinalReturnWorkspace seeds {specializationBudget := 256, compilationFuel := 1000})
  let key (name : String) : IO Key := match nonFinalReturnNames.findIdx? (· == name) with
    | some index => match compiled.keys[index]? with
      | some key => pure key
      | none => throw (IO.userError s!"non-final return root {name} missing")
    | none => throw (IO.userError s!"non-final return {name} unknown")
  let mut session ← boot (← compiled.open)
  for (name, expected) in [("blockEarly", word 1), ("lastInBranch", word 1)] do
    let completed ← execute session (← key name) []
    require (completed.value == expected) s!"{name} gave {reprStr completed.value}"
    session := completed.session
  let _ := session
  refusedNonFinalReturn "two returns"
    ["function bad() returns (Word) { return 1; return 2; }"]
  refusedNonFinalReturn "a let after a return"
    ["function bad() returns (Word) { return 1; let x: Word = 2; }"]
  refusedNonFinalReturn "a block"
    ["function bad() returns (Word) { let x: Word = 0; { return 1; x = 2; } return x; }"]
  refusedNonFinalReturn "an if body"
    ["function bad(flag: Bool) returns (Word) { let x: Word = 0; if (flag) { return 1; x = 2; } return x; }"]
  refusedNonFinalReturn "an else body"
    ["function bad(flag: Bool) returns (Word) { let x: Word = 0; if (flag) { x = 1; } else { return 2; x = 3; } return x; }"]
  refusedNonFinalReturn "a match arm"
    ["function bad(b: Bool) returns (Word) { match (b) { case true { return 1; b = false; } case false { return 2; } } }"]
  refusedNonFinalReturn "a while body"
    ["function bad(flag: Bool) returns (Word) { let x: Word = 0; while (flag) { return 1; x = 2; } return x; }"]
  refusedNonFinalReturn "a for body"
    ["function bad() returns (Word) { let x: Word = 0; for (let i: Word = 0; false; i = 1) { return 1; x = 2; } return x; }"]
  refusedNonFinalReturn "a lambda"
    ["function bad() returns (Word) { let f = lam (x: Word) -> Word { return x; return 2; }; return f(1); }"]
  refusedNonFinalReturn "a unit return"
    ["function bad() { return; let x: Word = 1; }"]
  refusedNonFinalReturn "a function nothing calls"
    ["function dead() returns (Word) { return 1; return 2; }",
      "function main() returns (Word) { return 5; }"]
  refusedNonFinalReturn "an implementation method"
    ["trait Add<T> { function add(left: T, right: T) returns (T); }", "enum Box { Only }",
      "impl Add<Box> { function add(left: Box, right: Box) returns (Box) { return left; return right; } }"]
  IO.println "SOURCE_CORE_NON_FINAL_RETURN_PASS: upstream's SC0222 through the public API, a return that another statement of its sequence follows refused in a body, a block, an if and an else body, a match arm, a while and a for body, a lambda, a unit function, a function nothing calls and an implementation method, and a block that ends in a return accepted with statements after it, returning early, as a return last in its branch is"

/-- Step 8e's fixture: the functions of upstream's `checked-arith`,
`unchecked-scope`, `shift-operators`, `int-ops` and `issue92-checked-defaults`
fixtures (`tests/e2e/*/main.sol` at e2eef194) that need no conversion and no
contract storage, as top-level functions, and the ones that convert only to
reach a type adapted where the meaning is kept: `uint256(0)` is `0` at
`uint256`, a `Typedef.abs(Typedef.rep(s))` amount or value is a parameter of
the converted type, and a result converted to `uint256` is returned at its own
type, whose word the API returns. Step 9a adds `basic`'s `bnoteq`, its one
`~=` that needs no contract storage. Step 9b's first part ports `afterBlock`,
`ltSigned` and `runtimePatterns` again as upstream wrote them, with `uint256(w)`,
and its second part ports `narrowAmount`, `wordShift`, `mulNeg`, `divSigned`,
`explicitWord` and `negI8` … `negI256` again as upstream wrote them, with
`Typedef.abs` and `Typedef.rep`, so none stays adapted. The lane's notes have
the table. -/
private def fixtureWorkspace : Workspace.RawWorkspace := workspaceOf [
  "function addU256(a: uint256, b: uint256) returns (uint256) { return a + b; }",
  "function subU256(a: uint256, b: uint256) returns (uint256) { return a - b; }",
  "function mulU256(a: uint256, b: uint256) returns (uint256) { return a * b; }",
  "function divU256(a: uint256, b: uint256) returns (uint256) { return a / b; }",
  "function modU256(a: uint256, b: uint256) returns (uint256) { return a % b; }",
  "function addU8(a: uint8, b: uint8) returns (uint8) { return a + b; }",
  "function subU8(a: uint8, b: uint8) returns (uint8) { return a - b; }",
  "function mulU8(a: uint8, b: uint8) returns (uint8) { return a * b; }",
  "function divU8(a: uint8, b: uint8) returns (uint8) { return a / b; }",
  "function modU8(a: uint8, b: uint8) returns (uint8) { return a % b; }",
  "function addI256(a: int256, b: int256) returns (int256) { return a + b; }",
  "function subI256(a: int256, b: int256) returns (int256) { return a - b; }",
  "function mulI256(a: int256, b: int256) returns (int256) { return a * b; }",
  "function divI256(a: int256, b: int256) returns (int256) { return a / b; }",
  "function modI256(a: int256, b: int256) returns (int256) { return a % b; }",
  "function addI8(a: int8, b: int8) returns (int8) { return a + b; }",
  "function subI8(a: int8, b: int8) returns (int8) { return a - b; }",
  "function mulI8(a: int8, b: int8) returns (int8) { return a * b; }",
  "function divI8(a: int8, b: int8) returns (int8) { return a / b; }",
  "function modI8(a: int8, b: int8) returns (int8) { return a % b; }",
  "function checkedSum(a: uint256, b: uint256) returns (uint256) { return a + b; }",
  "function apply(f: function (uint256) returns (uint256), x: uint256) returns (uint256) { return f(x); }",
  "function outside(a: uint256, b: uint256) returns (uint256) { return a + b; }",
  "function inside(a: uint256, b: uint256) returns (uint256) { unchecked { return a + b; } }",
  "function compoundInside(a: uint256, b: uint256) returns (uint256) { let r: uint256 = a; unchecked { r -= b; } return r; }",
  "function afterBlock(a: uint256, b: uint256) returns (uint256) { let wrapped: uint256 = uint256(0); unchecked { wrapped = a + b; } return wrapped + a + b; }",
  "function calledFunction(a: uint256, b: uint256) returns (uint256) { unchecked { return checkedSum(a, b); } }",
  "function lambdaBody(a: uint256, b: uint256) returns (uint256) { unchecked { return apply(lam (v: uint256) -> uint256 { return v + b; }, a); } }",
  "function divisionByZero(a: uint256, b: uint256) returns (uint256) { unchecked { return a / b; } }",
  "function literalAmount(x: uint256) returns (uint256) { return x << 3; }",
  "function narrowAmount(x: uint256, s: uint256) returns (uint256) { let k: uint8 = Typedef.abs(Typedef.rep(s)); return x >> k; }",
  "function wordShift(x: uint256, s: uint256) returns (uint256) { let w: Word = Typedef.rep(x); return uint256(w << Typedef.rep(s)); }",
  "function compound(x: uint256, s: uint256) returns (uint256) { let r: uint256 = x; r <<= s; r >>= 1; return r; }",
  "function neverReverts(x: uint256) returns (uint256) { return x << 255; }",
  "function insideUnchecked(x: uint256, s: uint256) returns (uint256) { unchecked { return x << s; } }",
  "function precedence(a: uint256, b: uint256) returns (uint256) { return a + b << 2 & 0xff; }",
  "function comparisons(a: uint256, b: uint256) returns (bool) { return a > b && a >= b; }",
  "function negate8(x: int8) returns (int8) { return 0 - x; }",
  "function addI32(a: int32, b: int32) returns (int32) { return a + b; }",
  "function mulNeg() returns (uint256) { let d: int256 = 5; return uint256(Typedef.rep((0 - d) * d)); }",
  "function ltSigned() returns (uint256) { let d: int256 = 5; let e: int256 = 0 - d; if (e < d) { return uint256(1); } else { return uint256(0); } }",
  "function divSigned() returns (uint256) { let m20: int256 = 0 - 20; let three: int256 = 3; return uint256(Typedef.rep(m20 / three)); }",
  "function implicitSuccess() returns (bool) { let value = 6; value *= 7; return value == 42; }",
  "function negateSigned(value: int256) returns (int256) { return -value; }",
  "function negateWord(value: Word) returns (Word) { return -value; }",
  "function runtimePatterns(choice: uint256) returns (uint256, uint256) { let value = 0; if (choice == 1) { value = 1; } if (choice == 2) { value = 2; } let inferred: Word; match (value) { case 0 { inferred = 10; } case 1 { inferred = 20; } case _ { inferred = 30; } } let typed: Word; match (choice) { case 0 { typed = 10; } case 1 { typed = 20; } case _ { typed = 30; } } return (uint256(inferred), uint256(typed)); }",
  "function implicitAdd(fail: bool) returns (bool) { let x = 41; if (fail) { x = 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff; } let result = x + 1; return result == 42; }",
  "function implicitSub(fail: bool) returns (bool) { let x = 1; if (fail) { x = 0; } let result = x - 1; return result == 0; }",
  "function implicitMul(fail: bool) returns (bool) { let x = 21; if (fail) { x = 0x8000000000000000000000000000000000000000000000000000000000000000; } let result = x * 2; return result == 42; }",
  "function implicitDiv(fail: bool) returns (bool) { let divisor = 2; if (fail) { divisor = 0; } let result = 84 / divisor; return result == 42; }",
  "function implicitMod(fail: bool) returns (bool) { let divisor = 5; if (fail) { divisor = 0; } let result = 42 % divisor; return result == 2; }",
  "function implicitNeg(fail: bool) returns (bool) { let x = 0; if (fail) { x = 1; } let result = -x; return result == 0; }",
  "function implicitCompound(failure: uint256) returns (bool) { let x = 6; if (failure == 1) { x = 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff; } x += 1; if (failure == 2) { x = 0; } x -= 1; if (failure == 3) { x = 0x8000000000000000000000000000000000000000000000000000000000000000; } x *= 7; let divisor = 1; if (failure == 4) { divisor = 0; } x /= divisor; if (failure == 5) { divisor = 0; } x %= divisor; return x == 0; }",
  "function explicitWord(raw: uint256) returns (uint256, uint256, uint256) { let x: Word = Typedef.rep(raw); return (uint256(x + 1), uint256(x - 1), uint256(-x)); }",
  "function negUnsigned(x: uint256) returns (uint256) { return -x; }",
  "function negI8(raw: uint256) returns (uint256) { let x: int8 = Typedef.abs(Typedef.rep(raw)); return uint256(Typedef.rep(-x)); }",
  "function negI16(raw: uint256) returns (uint256) { let x: int16 = Typedef.abs(Typedef.rep(raw)); return uint256(Typedef.rep(-x)); }",
  "function negI32(raw: uint256) returns (uint256) { let x: int32 = Typedef.abs(Typedef.rep(raw)); return uint256(Typedef.rep(-x)); }",
  "function negI64(raw: uint256) returns (uint256) { let x: int64 = Typedef.abs(Typedef.rep(raw)); return uint256(Typedef.rep(-x)); }",
  "function negI128(raw: uint256) returns (uint256) { let x: int128 = Typedef.abs(Typedef.rep(raw)); return uint256(Typedef.rep(-x)); }",
  "function negI256(raw: uint256) returns (uint256) { let x: int256 = Typedef.abs(Typedef.rep(raw)); return uint256(Typedef.rep(-x)); }",
  "function bnoteq(x: uint256) returns (uint256) { let acc: uint256 = x; acc ~=; return acc; }"]

private def fixtureNames : List String := [
  "addU256", "subU256", "mulU256", "divU256", "modU256", "addU8", "subU8", "mulU8", "divU8", "modU8",
  "addI256", "subI256", "mulI256", "divI256", "modI256", "addI8", "subI8", "mulI8", "divI8", "modI8",
  "checkedSum", "apply", "outside", "inside", "compoundInside", "afterBlock", "calledFunction", "lambdaBody",
  "divisionByZero", "literalAmount", "narrowAmount", "wordShift", "compound", "neverReverts", "insideUnchecked",
  "precedence", "comparisons", "negate8", "addI32", "mulNeg", "ltSigned", "divSigned", "implicitSuccess",
  "negateSigned", "negateWord", "runtimePatterns", "implicitAdd", "implicitSub", "implicitMul", "implicitDiv",
  "implicitMod", "implicitNeg", "implicitCompound", "explicitWord", "negUnsigned", "negI8", "negI16", "negI32",
  "negI64", "negI128", "negI256", "bnoteq"]

/-- Step 8e, the upstream fixtures' cases through the public API: each value
and each panic code is the fixture's. -/
def runUpstreamFixtures : IO Unit := do
  let program ← get "upstream fixture check" (checkProgram fixtureWorkspace)
  let seeds ← fixtureNames.mapM (seed program)
  let compiled ← get "upstream fixture compilation"
    (compile fixtureWorkspace seeds {specializationBudget := 256, compilationFuel := 1000})
  let key (name : String) : IO Key := match fixtureNames.findIdx? (· == name) with
    | some index => match compiled.keys[index]? with
      | some key => pure key
      | none => throw (IO.userError s!"upstream fixture root {name} missing")
    | none => throw (IO.userError s!"upstream fixture {name} unknown")
  let max := modulus - 1
  let mut session ← boot (← compiled.open)
  let cases : List (String × List Value × Value) := [
    -- checked-arith, in range.
    ("addU256", [word max, word 0], word max), ("subU256", [word 5, word 3], word 2),
    ("mulU256", [word max, word 1], word max), ("divU256", [word 7, word 2], word 3),
    ("modU256", [word 7, word 3], word 1),
    ("addU8", [word 255, word 0], word 255), ("subU8", [word 10, word 3], word 7),
    ("mulU8", [word 15, word 17], word 255), ("divU8", [word 255, word 2], word 127),
    ("modU8", [word 255, word 16], word 15),
    ("addI256", [word (2 ^ 255 - 1), word 0], word (2 ^ 255 - 1)), ("subI256", [word (2 ^ 255), word 0], word (2 ^ 255)),
    ("mulI256", [word (2 ^ 255 - 1), word 1], word (2 ^ 255 - 1)),
    ("divI256", [word (modulus - 20), word 3], word (modulus - 6)),
    ("modI256", [word (modulus - 20), word 3], word (modulus - 2)),
    ("addI8", [word 127, word 0], word 127), ("subI8", [word (modulus - 128), word 0], word (modulus - 128)),
    ("mulI8", [word (modulus - 128), word 1], word (modulus - 128)),
    ("divI8", [word (modulus - 20), word 3], word (modulus - 6)),
    ("modI8", [word (modulus - 20), word 3], word (modulus - 2)),
    -- unchecked-scope: only operators written in the block wrap.
    ("inside", [word max, word 1], word 0), ("inside", [word 2, word 3], word 5),
    ("compoundInside", [word 0, word 1], word max),
    -- shift-operators.
    ("literalAmount", [word 5], word 40), ("narrowAmount", [word 0x100, word 4], word 0x10),
    ("narrowAmount", [word 0x100, word 255], word 0), ("wordShift", [word 1, word 255], word (2 ^ 255)),
    ("wordShift", [word 1, word 256], word 0), ("compound", [word 1, word 8], word 128),
    ("neverReverts", [word max], word (2 ^ 255)), ("insideUnchecked", [word 3, word 1], word 6),
    ("precedence", [word 1, word 2], word 12), ("precedence", [word 0x40, word 0], word 0),
    ("comparisons", [word 2, word 1], boolean true), ("comparisons", [word 1, word 2], boolean false),
    -- int-ops, as two's-complement words.
    ("mulNeg", [], word (modulus - 25)), ("ltSigned", [], word 1), ("divSigned", [], word (modulus - 6)),
    ("negate8", [word (modulus - 8)], word 8), ("addI32", [word 1000000000, word 1000000000], word 2000000000),
    -- issue92-checked-defaults: open literals default to `uint256`, checked.
    ("implicitSuccess", [], boolean true), ("negateSigned", [word (modulus - 42)], word 42),
    ("negateWord", [word 1], word max),
    ("runtimePatterns", [word 0], .product (word 10) (word 10)),
    ("runtimePatterns", [word 1], .product (word 20) (word 20)),
    ("runtimePatterns", [word 2], .product (word 30) (word 30)),
    ("implicitAdd", [boolean false], boolean true), ("implicitSub", [boolean false], boolean true),
    ("implicitMul", [boolean false], boolean true), ("implicitDiv", [boolean false], boolean true),
    ("implicitMod", [boolean false], boolean true), ("implicitNeg", [boolean false], boolean true),
    ("implicitCompound", [word 0], boolean true),
    ("explicitWord", [word 0], .product (word 1) (.product (word max) (word 0))),
    ("explicitWord", [word 1], .product (word 2) (.product (word 0) (word max))),
    ("explicitWord", [word max], .product (word 0) (.product (word (max - 1)) (word 1))),
    ("negUnsigned", [word 0], word 0),
    ("negI8", [word 0], word 0), ("negI8", [word max], word 1), ("negI8", [word 127], word (modulus - 127)),
    ("negI16", [word 0], word 0), ("negI16", [word max], word 1), ("negI16", [word 32767], word (modulus - 32767)),
    ("negI32", [word 0], word 0), ("negI32", [word max], word 1),
    ("negI32", [word 2147483647], word (modulus - 2147483647)),
    ("negI64", [word 0], word 0), ("negI64", [word max], word 1),
    ("negI64", [word 9223372036854775807], word (modulus - 9223372036854775807)),
    ("negI128", [word 0], word 0), ("negI128", [word max], word 1),
    ("negI128", [word (2 ^ 127 - 1)], word (modulus - (2 ^ 127 - 1))),
    ("negI256", [word 0], word 0), ("negI256", [word max], word 1),
    ("negI256", [word (2 ^ 255 - 1)], word (2 ^ 255 + 1)),
    -- basic: `bnoteq(10)` is `~10`.
    ("bnoteq", [word 10], word (modulus - 11))]
  for (name, arguments, expected) in cases do
    let completed ← execute session (← key name) arguments
    require (completed.value == expected) s!"{name} on {reprStr arguments} gave {reprStr completed.value}"
    session := completed.session
  -- `Panic(0x11)`: checked overflow, underflow and `MIN / -1`, after an `unchecked` block, in a
  -- called function and in a lambda body written in a block, and checked negation.
  let arithmetic : List (String × List Value) := [
    ("addU256", [word max, word 1]), ("subU256", [word 0, word 1]), ("mulU256", [word (2 ^ 255), word 2]),
    ("addU8", [word 200, word 100]), ("subU8", [word 0, word 1]), ("mulU8", [word 16, word 16]),
    ("addI256", [word (2 ^ 255 - 1), word 1]), ("subI256", [word (2 ^ 255), word 1]),
    ("mulI256", [word (2 ^ 255 - 1), word 2]), ("divI256", [word (2 ^ 255), word max]),
    ("addI8", [word 127, word 1]), ("subI8", [word (modulus - 128), word 1]), ("mulI8", [word 64, word 2]),
    ("divI8", [word (modulus - 128), word max]),
    ("outside", [word max, word 1]), ("afterBlock", [word max, word 1]), ("calledFunction", [word max, word 1]),
    ("lambdaBody", [word max, word 1]),
    ("implicitAdd", [boolean true]), ("implicitSub", [boolean true]), ("implicitMul", [boolean true]),
    ("implicitNeg", [boolean true]),
    ("implicitCompound", [word 1]), ("implicitCompound", [word 2]), ("implicitCompound", [word 3]),
    ("negUnsigned", [word 1]),
    ("negI8", [word (modulus - 128)]), ("negI16", [word (modulus - 32768)]), ("negI32", [word (modulus - 2 ^ 31)]),
    ("negI64", [word (modulus - 2 ^ 63)]), ("negI128", [word (modulus - 2 ^ 127)]), ("negI256", [word (2 ^ 255)])]
  for (name, arguments) in arithmetic do
    session ← panics session (← key name) arguments SourceCorePanics.arithmetic s!"{name} on {reprStr arguments}"
  -- `Panic(0x12)`: a zero divisor, inside an `unchecked` block too.
  let zero : List (String × List Value) := [
    ("divU256", [word 7, word 0]), ("modU256", [word 7, word 0]), ("divU8", [word 5, word 0]),
    ("modU8", [word 5, word 0]), ("divI256", [word 5, word 0]), ("modI256", [word 5, word 0]),
    ("divI8", [word 5, word 0]), ("modI8", [word 5, word 0]), ("divisionByZero", [word 7, word 0]),
    ("implicitDiv", [boolean true]), ("implicitMod", [boolean true]),
    ("implicitCompound", [word 4]), ("implicitCompound", [word 5])]
  for (name, arguments) in zero do
    session ← panics session (← key name) arguments SourceCorePanics.divisionByZero s!"{name} on {reprStr arguments}"
  IO.println "SOURCE_CORE_UPSTREAM_INTEGER_FIXTURES_PASS: the cases of upstream's checked-arith, unchecked-scope, shift-operators, int-ops and issue92-checked-defaults fixtures that need no contract storage, with afterBlock, ltSigned, runtimePatterns, narrowAmount, wordShift, mulNeg, divSigned, explicitWord and negI8 … negI256 as upstream wrote them with uint256(w), Typedef.abs and Typedef.rep, so none stays adapted, and basic's bnoteq, give the fixtures' values and panic codes"

/-- Row 4's step 8: the 34 functions of upstream's `mem-array`, `array-syntax`, `array-slice` and
`memory-array-abi` fixtures (`tests/e2e/*/main.sol` at e2eef194) that Lean's native pipeline can
run, as upstream wrote them, with the contracts' methods as functions: mem-array's 11, `bump(r)`
included; array-syntax's `sumAll`, `pair`, `local`, `returned`, `nested` and `callResultLength`;
array-slice's `build()` and its 11 public functions that need no storage; and memory-array-abi's
`ret`, `sum`, `echo`, `grid` and `slices`. Those five take or give arrays, so word wrappers call
them: `retAt(n, i)` and `retLength(n)` read `ret(n)`, `sumFour(a, b, c, d)` and `sumNone()` pass
`sum` a literal, `echoAt(x0, x1, i)` and `echoLength(x0, x1)` read `echo([x0, x1])`,
`gridLength(n)`, `gridRowLength(n, i)` and `gridAt(n, i, j)` read `grid(n)`, and
`slicesAt(x0, x1, x2, x3, i)` reads `slices([x0, x1, x2, x3])`. The wrappers change only how an
array arrives, a literal of word arguments instead of the ABI's decoding, and how one leaves, read
back by index or length instead of ABI-encoded. -/
private def arrayPortWorkspace : Workspace.RawWorkspace := workspaceOf [
  "function bump(r: memref<uint256>) {",
  "    let v: uint256 = CanStore.load(r);",
  "    CanStore.store(r, v + uint256(1));",
  "}",
  "function newLen(n: uint256) returns (uint256) {",
  "  let m: uint256[] = new uint256[](n);",
  "  return Length.length(m);",
  "}",
  "function setGet(n: uint256, i: uint256, v: uint256) returns (uint256) {",
  "    let m: uint256[] = new uint256[](n);",
  "    m[i] = v;",
  "    return m[i];",
  "}",
  "function defaultZero(n: uint256, i: uint256) returns (uint256) {",
  "  let m: uint256[] = new uint256[](n);",
  "  return m[i];",
  "}",
  "function oversized(n: uint256) returns (uint256) {",
  "  let m: uint256[] = new uint256[](n);",
  "  return Length.length(m);",
  "}",
  "function fillAndSum(n: uint256) returns (uint256) {",
  "    let m: uint256[] = new uint256[](n);",
  "    for (let i: uint256 = 0; i < n; i += 1) {",
  "        m[i] = i * 5;",
  "    }",
  "    let total: uint256 = 0;",
  "    for (let i: uint256 = 0; i < n; i += 1) {",
  "        total += m[i];",
  "    }",
  "    return total;",
  "}",
  "function compound(v: uint256) returns (uint256) {",
  "    let m: uint256[] = [v, uint256(1)];",
  "    m[0] += 3;",
  "    return m[0];",
  "}",
  "function nestedEmpty(n: uint256) returns (uint256) {",
  "  let rows: uint256[][] = new uint256[][](n);",
  "  return Length.length(rows[n - 1]);",
  "}",
  "function nestedReplace(n: uint256, v: uint256) returns (uint256) {",
  "    let rows: uint256[][] = new uint256[][](2);",
  "    let row: uint256[] = new uint256[](n);",
  "    row[n - 1] = v;",
  "    rows[1] = row;",
  "    return rows[1][n - 1] + Length.length(rows[0]);",
  "}",
  "function alias(v: uint256) returns (uint256) {",
  "    let m: uint256[] = [uint256(1), uint256(2)];",
  "    let n: uint256[] = m;",
  "    n[1] = v;",
  "    return m[1];",
  "}",
  "function bumpElement(v: uint256) returns (uint256) {",
  "    let m: uint256[] = new uint256[](2);",
  "    m[1] = v;",
  "    bump(lidx(m, uint256(1)));",
  "    return m[1];",
  "}",
  "function sumAll(xs: uint256[]) returns (uint256) {",
  "    let total: uint256 = 0;",
  "    for (let i: uint256 = 0; i < xs.length; i += 1) {",
  "        total += xs[i];",
  "    }",
  "    return total;",
  "}",
  "function pair(a: uint256, b: uint256) returns (uint256[]) {",
  "    return [a, b];",
  "}",
  "function local(a: uint256, b: uint256) returns (uint256) {",
  "    let m: uint256[] = [a, b, a];",
  "    return sumAll(m);",
  "}",
  "function returned(a: uint256, b: uint256) returns (uint256) {",
  "    let m: uint256[] = pair(a, b);",
  "    return m[1];",
  "}",
  "function nested() returns (uint256) {",
  "    let rows: uint256[][] = [[uint256(1), uint256(2)], [uint256(3)]];",
  "    return rows[0][1] + rows[1][0];",
  "}",
  "function callResultLength(n: uint256) returns (uint256) {",
  "    return pair(n, n).length + new uint256[](n).length - 2;",
  "}",
  "function build() returns (uint256[]) {",
  "    let a: uint256[] = new uint256[](5);",
  "    for (let i: uint256 = 0; i < a.length; i += 1) {",
  "        a[i] = i + 10;",
  "    }",
  "    return a;",
  "}",
  "function rangeLen() returns (uint256) {",
  "    return build()[1:4].length;",
  "}",
  "function rangeGet(i: uint256) returns (uint256) {",
  "    return build()[1:4][i];",
  "}",
  "function fromLen(start: uint256) returns (uint256) {",
  "    return build()[start:].length;",
  "}",
  "function toLen(end: uint256) returns (uint256) {",
  "    return build()[:end].length;",
  "}",
  "function allLen() returns (uint256) {",
  "    return build()[:].length;",
  "}",
  "function reslice(i: uint256) returns (uint256) {",
  "    return build()[1:4][1:][i];",
  "}",
  "function bounds(start: uint256, end: uint256) returns (uint256) {",
  "    return build()[start:end].length;",
  "}",
  "function materialise(i: uint256) returns (uint256) {",
  "    let b: uint256[] = toArray(build()[1:4]);",
  "    return b[i];",
  "}",
  "function aliasing() returns (uint256) {",
  "    let a = build();",
  "    let s = a[2:];",
  "    a[3] = 99;",
  "    return s[1];",
  "}",
  "function spec() returns (uint256) {",
  "    let a = build();",
  "    let full = a[:];",
  "    let front = a[:2];",
  "    let back = a[3:];",
  "    let mid = a[1:4];",
  "    let inner = mid[1:];",
  "    return full.length + front.length + back.length + mid.length + inner.length + mid[0] + inner[1];",
  "}",
  "function ternaryBound(c: bool) returns (uint256) {",
  "    return build()[c ? uint256(1) : uint256(2):].length;",
  "}",
  "function ret(n: uint256) returns (uint256[]) {",
  "    let a = new uint256[](n);",
  "    for (let i: uint256 = 0; i < n; i += 1) {",
  "        a[i] = i * 2;",
  "    }",
  "    return a;",
  "}",
  "function sum(xs: uint256[]) returns (uint256) {",
  "    let s: uint256 = 0;",
  "    for (let i: uint256 = 0; i < xs.length; i += 1) {",
  "        s += xs[i];",
  "    }",
  "    return s;",
  "}",
  "function echo(xs: uint256[]) returns (uint256[]) {",
  "    for (let i: uint256 = 0; i < xs.length; i += 1) {",
  "        xs[i] += 1;",
  "    }",
  "    return xs;",
  "}",
  "function grid(n: uint256) returns (uint256[][]) {",
  "    let g = new uint256[][](n);",
  "    g[n - 1] = new uint256[](1);",
  "    return g;",
  "}",
  "function slices(xs: uint256[]) returns (uint256[]) {",
  "    return toArray(xs[1:3]);",
  "}",
  "function retAt(n: uint256, i: uint256) returns (uint256) {",
  "    return ret(n)[i];",
  "}",
  "function retLength(n: uint256) returns (uint256) {",
  "    return ret(n).length;",
  "}",
  "function sumFour(a: uint256, b: uint256, c: uint256, d: uint256) returns (uint256) {",
  "    return sum([a, b, c, d]);",
  "}",
  "function sumNone() returns (uint256) {",
  "    return sum([]);",
  "}",
  "function echoAt(x0: uint256, x1: uint256, i: uint256) returns (uint256) {",
  "    return echo([x0, x1])[i];",
  "}",
  "function echoLength(x0: uint256, x1: uint256) returns (uint256) {",
  "    return echo([x0, x1]).length;",
  "}",
  "function gridLength(n: uint256) returns (uint256) {",
  "    return grid(n).length;",
  "}",
  "function gridRowLength(n: uint256, i: uint256) returns (uint256) {",
  "    return grid(n)[i].length;",
  "}",
  "function gridAt(n: uint256, i: uint256, j: uint256) returns (uint256) {",
  "    return grid(n)[i][j];",
  "}",
  "function slicesAt(x0: uint256, x1: uint256, x2: uint256, x3: uint256, i: uint256) returns (uint256) {",
  "    return slices([x0, x1, x2, x3])[i];",
  "}"]

/-- Row 4's own array cases, not upstream's. From steps 2b-iii and 3c: `nestedLengths(n)`, a
nested `new` with the other two spellings of a length, and `signedIndex(n)`, a read at a negative
`int8` index. From step 5a-iii-a: `placeFirst(i, v)` checks its place before a right side that
divides by zero, `writeBack(i, j, v)` writes an element of one row of two and reads both rows
back, and `throughLocal(v)` writes a call's result through a local, which writes the caller's array
(difference 16). From step 5b: the lane's probe's `compoundTwice()` runs its place's `next(c)` once
(difference 1) and `plainOnce()` writes through it once; `snapshotFirst(v)` reads its element
before a right side that writes it; `boundsFirst(i, v)` panics with `0x32` before a right side that
divides by zero; `narrow` and `narrowUnchecked` add at a `uint8` element, checked and in an
`unchecked` block; `divide` divides an element by zero; `shifted` shifts a `uint8` element;
`invertedU8`, `invertedU256` and `invertedI8` take `~=` on an element; `bits` takes `|= &= ^=`;
`nestedAdd(i, j, v)` adds to an element of one row of two; and `headerForms()` takes `+=` and `~=`
on an element in `for` headers. -/
private def arrayCaseWorkspace : Workspace.RawWorkspace := workspaceOf [
  "function nestedLengths(n: uint256) returns (uint256) {",
  "  let grid = new int8[][](n);",
  "  return grid.length + new uint8[](3).length();",
  "}",
  "function signedIndex(n: uint256) returns (uint256) {",
  "  let m: uint256[] = new uint256[](n);",
  "  let k: int8 = -1;",
  "  return m[k];",
  "}",
  "function placeFirst(i: uint256, v: uint256) returns (uint256) {",
  "    let m: uint256[] = new uint256[](2);",
  "    m[i] = v / (v - v);",
  "    return m[0];",
  "}",
  "function writeBack(i: uint256, j: uint256, v: uint256) returns (uint256) {",
  "    let rows: uint256[][] = [new uint256[](2), new uint256[](2)];",
  "    rows[i][j] = v;",
  "    return rows[i][j] * 10 + rows[1 - i][j];",
  "}",
  "function same(xs: uint256[]) returns (uint256[]) {",
  "    return xs;",
  "}",
  "function throughLocal(v: uint256) returns (uint256) {",
  "    let m: uint256[] = new uint256[](2);",
  "    let r: uint256[] = same(m);",
  "    r[1] = v;",
  "    return m[1];",
  "}",
  "function next(c: uint256[]) returns (uint256) {",
  "    c[0] += 1;",
  "    return 0;",
  "}",
  "function compoundTwice() returns (uint256) {",
  "    let c: uint256[] = new uint256[](1);",
  "    let m: uint256[] = new uint256[](1);",
  "    m[next(c)] += 5;",
  "    return c[0] * 100 + m[0];",
  "}",
  "function plainOnce() returns (uint256) {",
  "    let c: uint256[] = new uint256[](1);",
  "    let m: uint256[] = new uint256[](1);",
  "    m[next(c)] = 7;",
  "    return c[0] * 100 + m[0];",
  "}",
  "function overwrite(m: uint256[]) returns (uint256) {",
  "    m[0] = 100;",
  "    return 1;",
  "}",
  "function snapshotFirst(v: uint256) returns (uint256) {",
  "    let m: uint256[] = [v];",
  "    m[0] += overwrite(m);",
  "    return m[0];",
  "}",
  "function boundsFirst(i: uint256, v: uint256) returns (uint256) {",
  "    let m: uint256[] = new uint256[](2);",
  "    m[i] += v / (v - v);",
  "    return m[0];",
  "}",
  "function narrow(a: uint8, b: uint8) returns (uint8) {",
  "    let m: uint8[] = [a];",
  "    m[0] += b;",
  "    return m[0];",
  "}",
  "function narrowUnchecked(a: uint8, b: uint8) returns (uint8) {",
  "    let m: uint8[] = [a];",
  "    unchecked { m[0] += b; }",
  "    return m[0];",
  "}",
  "function divide(a: uint256, b: uint256) returns (uint256) {",
  "    let m: uint256[] = [a];",
  "    m[0] /= b;",
  "    return m[0];",
  "}",
  "function shifted(a: uint8, s: uint256) returns (uint8) {",
  "    let m: uint8[] = [a];",
  "    m[0] <<= s;",
  "    return m[0];",
  "}",
  "function invertedU8(a: uint8) returns (uint8) {",
  "    let m: uint8[] = [a];",
  "    m[0] ~=;",
  "    return m[0];",
  "}",
  "function invertedU256(a: uint256) returns (uint256) {",
  "    let m: uint256[] = [a];",
  "    m[0] ~=;",
  "    return m[0];",
  "}",
  "function invertedI8(a: int8) returns (int8) {",
  "    let m: int8[] = [a];",
  "    m[0] ~=;",
  "    return m[0];",
  "}",
  "function bits(a: uint256) returns (uint256) {",
  "    let m: uint256[] = [a];",
  "    m[0] |= 6;",
  "    m[0] &= 3;",
  "    m[0] ^= 1;",
  "    return m[0];",
  "}",
  "function nestedAdd(i: uint256, j: uint256, v: uint256) returns (uint256) {",
  "    let rows: uint256[][] = [[uint256(1), uint256(2)], [uint256(3), uint256(4)]];",
  "    rows[i][j] += v;",
  "    return rows[0][j] * 100 + rows[1][j];",
  "}",
  "function headerForms() returns (uint256) {",
  "    let m: uint256[] = new uint256[](1);",
  "    for (let i: uint256 = 0; i < 2; m[0] += 1) {",
  "        i += 1;",
  "    }",
  "    for (let i: uint256 = 0; i < 1; m[0] ~=) {",
  "        i += 1;",
  "    }",
  "    return m[0];",
  "}"]

/-- The source semantics and the lowering reject the same first length with `Panic(0x41)`. -/
example : Solcore.SourceSemantics.Dynamic.newArrayLengthLimit =
    SourceCoreDataExpressions.arrayLengthLimit := rfl

private def arrayPortNames : List String := [
  "newLen", "oversized", "setGet", "defaultZero", "fillAndSum", "compound", "nestedEmpty",
  "nestedReplace", "alias", "bumpElement", "local", "returned", "nested", "callResultLength",
  "rangeLen", "rangeGet", "fromLen", "toLen", "allLen", "reslice", "bounds", "materialise",
  "aliasing", "spec", "ternaryBound", "retAt", "retLength", "sumFour", "sumNone", "echoAt",
  "echoLength", "gridLength", "gridRowLength", "gridAt", "slicesAt"]

/-- Row 4's step 8, the upstream array fixtures' cases through the public API, as row 1's step 8e
runs the integer fixtures': each value and each panic code is the fixture's. memory-array-abi's
arrays are read back through the wrappers: `ret(3) -> [0,2,4]` as 0, 2 and 4 at indexes 0 to 2
and length 3, `ret(0) -> []` as length 0, `sum([1,2,3,4]) -> 10` and `sum([]) -> 0` as those
sums, `echo([7,8]) -> [8,9]` as 8 at 0, 9 at 1 and length 2, `grid(2) -> [[],[0]]` as length 2,
rows of lengths 0 and 1 and 0 at `[1][0]`, and `slices([10,20,30,40]) -> [20,30]` as 20 at 0, 30
at 1 and `0x32` at 2. The earlier steps' own values on the same functions follow: lengths 0 and
1, the last index below a length, `0x32` from the length on, a negative index's word included,
and `0x41` from 2^251 − 1 on while 2^251 − 2 allocates (difference 2). -/
def runUpstreamArrayFixtures : IO Unit := do
  let program ← get "upstream array fixture check" (checkProgram arrayPortWorkspace)
  let seeds ← arrayPortNames.mapM (seed program)
  let compiled ← get "upstream array fixture compilation"
    (compile arrayPortWorkspace seeds {specializationBudget := 256, compilationFuel := 1000})
  let key (name : String) : IO Key := match arrayPortNames.findIdx? (· == name) with
    | some index => match compiled.keys[index]? with
      | some key => pure key
      | none => throw (IO.userError s!"upstream array fixture root {name} missing")
    | none => throw (IO.userError s!"upstream array fixture {name} unknown")
  let mut session ← boot (← compiled.open)
  let cases : List (String × List Value × Nat) := [
    -- mem-array.
    ("newLen", [word 5], 5), ("setGet", [word 3, word 1, word 99], 99),
    ("setGet", [word 3, word 0, word 7], 7), ("defaultZero", [word 4, word 2], 0),
    ("fillAndSum", [word 4], 30), ("compound", [word 10], 13), ("nestedEmpty", [word 3], 0),
    ("nestedReplace", [word 4, word 9], 9), ("alias", [word 8], 8), ("bumpElement", [word 7], 8),
    -- array-syntax.
    ("local", [word 3, word 4], 10), ("returned", [word 3, word 4], 4), ("nested", [], 5),
    ("callResultLength", [word 4], 4),
    -- array-slice.
    ("rangeLen", [], 3), ("rangeGet", [word 0], 11), ("rangeGet", [word 2], 13),
    ("fromLen", [word 2], 3), ("fromLen", [word 5], 0), ("toLen", [word 3], 3), ("allLen", [], 5),
    ("reslice", [word 0], 12), ("reslice", [word 1], 13), ("bounds", [word 2, word 2], 0),
    ("materialise", [word 0], 11), ("materialise", [word 2], 13), ("aliasing", [], 99),
    ("spec", [], 38), ("ternaryBound", [.bool true], 4), ("ternaryBound", [.bool false], 3),
    -- memory-array-abi, through the wrappers.
    ("retAt", [word 3, word 0], 0), ("retAt", [word 3, word 1], 2), ("retAt", [word 3, word 2], 4),
    ("retLength", [word 3], 3), ("retLength", [word 0], 0),
    ("sumFour", [word 1, word 2, word 3, word 4], 10), ("sumNone", [], 0),
    ("echoAt", [word 7, word 8, word 0], 8), ("echoAt", [word 7, word 8, word 1], 9),
    ("echoLength", [word 7, word 8], 2), ("gridLength", [word 2], 2),
    ("gridRowLength", [word 2, word 0], 0), ("gridRowLength", [word 2, word 1], 1),
    ("gridAt", [word 2, word 1, word 0], 0),
    ("slicesAt", [word 10, word 20, word 30, word 40, word 0], 20),
    ("slicesAt", [word 10, word 20, word 30, word 40, word 1], 30),
    -- The earlier steps' own values.
    ("newLen", [word 0], 0), ("oversized", [word (2 ^ 251 - 2)], 2 ^ 251 - 2),
    ("defaultZero", [word 4, word 3], 0), ("nestedEmpty", [word 1], 0),
    ("local", [word 1, word 2], 4), ("returned", [word 5, word 9], 9),
    ("callResultLength", [word 2], 2)]
  for (name, arguments, expected) in cases do
    let completed ← execute session (← key name) arguments
    require (completed.value == word expected) s!"{name} on {reprStr arguments} gave {reprStr completed.value}"
    session := completed.session
  -- `Panic(0x32)`: an index or a bound from its array's or its view's length on, a copy's included.
  let outOfBounds : List (String × List Value) := [
    ("setGet", [word 2, word 5, word 1]), ("rangeGet", [word 3]), ("fromLen", [word 6]),
    ("toLen", [word 6]), ("reslice", [word 2]), ("bounds", [word 4, word 2]),
    ("bounds", [word 0, word 6]), ("materialise", [word 3]),
    ("slicesAt", [word 10, word 20, word 30, word 40, word 2]),
    -- The earlier steps' own.
    ("defaultZero", [word 4, word 4]), ("defaultZero", [word 0, word 0]),
    ("defaultZero", [word 4, word (modulus - 1)]), ("echoAt", [word 7, word 8, word 2])]
  for (name, arguments) in outOfBounds do
    session ← panics session (← key name) arguments SourceCorePanics.outOfBounds
      s!"{name} on {reprStr arguments}"
  -- `Panic(0x41)`: the fixture's `oversized(2^251)`, then 2^251 − 1 and the largest word.
  for argument in [2 ^ 251, 2 ^ 251 - 1, modulus - 1] do
    session ← panics session (← key "oversized") [word argument] SourceCorePanics.allocation
      s!"oversized({argument})"
  IO.println "SOURCE_CORE_UPSTREAM_ARRAY_FIXTURES_PASS: the 34 functions of upstream's mem-array, array-syntax, array-slice and memory-array-abi fixtures that need no contract storage and no ABI, as upstream wrote them, give the fixtures' values and panic codes in one test: lengths, zeroed and written elements, sums, aliasing, 0x32 from an index's or a bound's length on, 0x41 for the fixture's oversized length, slices, their copies and a view of a later write, a memref's load and store, and a compound element assignment, with ret, sum, echo, grid and slices read back through word wrappers"

private def arrayCaseNames : List String := [
  "nestedLengths", "signedIndex", "placeFirst", "writeBack", "throughLocal", "compoundTwice",
  "plainOnce", "snapshotFirst", "boundsFirst", "narrow", "narrowUnchecked", "divide", "shifted",
  "invertedU8", "invertedU256", "invertedI8", "bits", "nestedAdd", "headerForms"]

/-- Row 4's own array cases through the public API: a nested `new`'s lengths; a negative `int8`
index panics with `0x32`; an element place panics with `0x32` from its array's length on, before
its right side runs, and a nested write or compound assignment changes only its row; a write
through a local reaches the caller's array; and a compound assignment or an in-place `~` on an
element evaluates its place once, so the probe's 205 is 105 (difference 1), reads the element
before its right side, and takes its type's checks with `0x11` and `0x12`, wraps and shifts, as on
a local. -/
def runArrayElementCases : IO Unit := do
  let program ← get "array element case check" (checkProgram arrayCaseWorkspace)
  let seeds ← arrayCaseNames.mapM (seed program)
  let compiled ← get "array element case compilation"
    (compile arrayCaseWorkspace seeds {specializationBudget := 256, compilationFuel := 1000})
  let key (name : String) : IO Key := match arrayCaseNames.findIdx? (· == name) with
    | some index => match compiled.keys[index]? with
      | some key => pure key
      | none => throw (IO.userError s!"array element case root {name} missing")
    | none => throw (IO.userError s!"array element case {name} unknown")
  let mut session ← boot (← compiled.open)
  let cases : List (String × List Nat × Nat) := [
    ("nestedLengths", [4], 7), ("writeBack", [0, 1, 7], 70), ("writeBack", [1, 0, 3], 30),
    ("throughLocal", [9], 9), ("compoundTwice", [], 105), ("plainOnce", [], 107),
    ("snapshotFirst", [5], 6), ("narrow", [200, 55], 255), ("narrowUnchecked", [200, 100], 44),
    ("divide", [7, 2], 3), ("shifted", [3, 7], 128), ("shifted", [1, 8], 0),
    ("invertedU8", [10], 245), ("invertedU256", [10], modulus - 11), ("invertedI8", [modulus - 1], 0),
    ("invertedI8", [0], modulus - 1), ("bits", [8], 3), ("nestedAdd", [0, 1, 5], 704),
    ("nestedAdd", [1, 0, 5], 108), ("headerForms", [], modulus - 3)]
  for (name, arguments, expected) in cases do
    let completed ← execute session (← key name) (arguments.map word)
    require (completed.value == word expected) s!"{name}({arguments}) gave {reprStr completed.value}"
    session := completed.session
  let outOfBounds : List (String × List Nat) := [
    ("signedIndex", [4]), ("placeFirst", [5, 1]), ("writeBack", [2, 0, 1]), ("writeBack", [0, 2, 1]),
    ("boundsFirst", [2, 1]), ("nestedAdd", [2, 0, 5]), ("nestedAdd", [0, 2, 5])]
  for (name, arguments) in outOfBounds do
    session ← panics session (← key name) (arguments.map word) SourceCorePanics.outOfBounds
      s!"{name}({arguments})"
  for (name, arguments) in [("placeFirst", [0, 1]), ("boundsFirst", [0, 1]), ("divide", [7, 0])] do
    session ← panics session (← key name) (arguments.map word) SourceCorePanics.divisionByZero
      s!"{name}({arguments})"
  let _ ← panics session (← key "narrow") [word 200, word 100] SourceCorePanics.arithmetic
    "narrow(200, 100)"
  IO.println "SOURCE_CORE_ARRAY_ELEMENT_CASES_PASS: row 4's own array cases give a nested new's lengths, 0x32 at a negative int8 index and from an element place's length on before its right side, a nested write or compound assignment that changes only its row and a write through a local that reaches the caller's array, and a compound assignment or an in-place ~ on an element that evaluates its place once (105 where upstream gives 205), reads the element before its right side, and takes its type's checks with 0x11 and 0x12, wraps and shifts"

def run : IO Unit := do
  let program ← get "fixed-width operator check" (checkProgram workspace)
  let seeds ← names.mapM (seed program)
  let compiled ← get "fixed-width operator compilation"
    (compile workspace seeds {specializationBudget := 256, compilationFuel := 1000})
  let key (index : Nat) : IO Key := match compiled.keys[index]? with
    | some key => pure key | none => throw (IO.userError "fixed-width operator root missing")
  let mut session ← boot (← compiled.open)
  let cases : List (Nat × List Value × Value) := [
    (0, [word 7, word 7], boolean true), (0, [word 255, word 0], boolean false),
    (1, [word (modulus - 1), word (modulus - 1)], boolean false), (1, [word 3, word (modulus - 3)], boolean true),
    (2, [word 4, word 9], boolean true), (2, [word 9, word 4], boolean false),
    (3, [word 9, word 9], boolean true), (3, [word (2 ^ 64 - 1), word 0], boolean false),
    (4, [word (2 ^ 128 - 1), word 1], boolean true), (4, [word 1, word 1], boolean false),
    (5, [word (modulus - 1), word (modulus - 1)], boolean true), (5, [word 0, word 1], boolean false),
    (6, [word 0xF0, word 0x3C], word 0x30),
    (7, [word 0xF000, word 0x00FF], word 0xF0FF),
    (8, [word 0xFFFF0000, word 0x0F0F0F0F], word 0xF0F00F0F),
    (9, [word (modulus - 1), word (modulus - 1)], boolean true), (9, [word (modulus - 1), word 1], boolean false),
    (10, [word 0xF0, word 0x3C], word 0xFC),
    (11, [word (modulus - 1), word 5], word 5), (11, [word (modulus - 128), word (modulus - 1)], word (modulus - 128)),
    (12, [word (modulus - 2), word 1], word (modulus - 1)), (12, [word 0x0F00, word 0x00F0], word 0x0FF0),
    (13, [word (modulus - 1), word 1], word (modulus - 2)),
    (14, [word 5], word (modulus - 6)), (14, [word (modulus - 128)], word 127),
    (15, [word 0], word (modulus - 1)),
    (16, [word 0], word (modulus - 1)), (16, [word (modulus - 1)], word 0),
    (17, [word (modulus - 1), word 1], boolean true), (17, [word 1, word (modulus - 1)], boolean false),
    (17, [word (modulus - 128), word 127], boolean true),
    (18, [word (modulus - 2), word (modulus - 3)], boolean true), (18, [word (modulus - 3), word (modulus - 2)], boolean false),
    (19, [word 0, word (modulus - 1)], boolean true), (19, [word (modulus - 1), word 0], boolean false),
    (20, [word (modulus - 5), word (modulus - 5)], boolean true), (20, [word 5, word (modulus - 5)], boolean false),
    (21, [word 0], word 255), (21, [word 255], word 0), (21, [word 0x0F], word 0xF0),
    (22, [word 0x1234], word 0xEDCB),
    (23, [word 0], word (2 ^ 128 - 1)), (23, [word (2 ^ 128 - 1)], word 0),
    (24, [word 200, word 55], word 255), (25, [word 5, word 3], word 2),
    (26, [word 65536, word 65535], word 4294901760),
    (27, [word (modulus - 1), word 0], word (modulus - 1)),
    (28, [word (2 ^ 128), word (2 ^ 128 - 1)], word (modulus - 2 ^ 128)),
    (29, [word 127, word 0], word 127), (29, [word (modulus - 100), word (modulus - 28)], word (modulus - 128)),
    (30, [word (modulus - 1), word 127], word (modulus - 128)),
    (31, [word (modulus - 64), word 2], word (modulus - 128)),
    (32, [word 5, word 7], word (modulus - 2)),
    (33, [word (2 ^ 127), word (2 ^ 127)], word (2 ^ 254)), (33, [word (modulus - 1), word (modulus - 1)], word 1),
    -- Checked compound assignment at the range edges, checked after the setter.
    (34, [word 200, word 55], word 255), (34, [word 0, word 0], word 0),
    (35, [word 5, word 5], word 0), (35, [word 255, word 1], word 254),
    (36, [word 15, word 17], word 255), (36, [word 0, word 255], word 0),
    (37, [word (modulus - 2), word 1], word (modulus - 1)),
    (38, [word 1, word 1], word 0), (38, [word (modulus - 1), word (modulus - 1)], word 0),
    (39, [word (2 ^ 128), word (2 ^ 128 - 1)], word (modulus - 2 ^ 128)),
    (40, [word 127, word 0], word 127), (40, [word (modulus - 100), word (modulus - 28)], word (modulus - 128)),
    (41, [word (modulus - 1), word 127], word (modulus - 128)), (41, [word 127, word 127], word 0),
    (42, [word (modulus - 64), word 2], word (modulus - 128)), (42, [word (modulus - 1), word (modulus - 127)], word 127),
    (43, [word (2 ^ 255 - 1), word 0], word (2 ^ 255 - 1)), (43, [word (2 ^ 255), word (2 ^ 255 - 1)], word (modulus - 1)),
    (44, [word (2 ^ 255), word 0], word (2 ^ 255)), (44, [word 0, word (2 ^ 255 - 1)], word (2 ^ 255 + 1)),
    (45, [word (modulus - 1), word (2 ^ 255 - 1)], word (2 ^ 255 + 1)), (45, [word (2 ^ 127), word (2 ^ 127)], word (2 ^ 254)),
    -- `&= |= ^=` are Word's on canonical words.
    (46, [word 0xF0, word 0x3C], word 0x30), (47, [word (modulus - 128), word 1], word (modulus - 127)),
    (48, [word 0xFFFF, word 0x00FF], word 0xFF00),
    -- A mapping element.
    (49, [word 200, word 55], word 255),
    -- Checked `/ %`: quotients round toward zero, remainders take the dividend's sign.
    (51, [word 255, word 16], word 15), (51, [word 7, word 7], word 1), (51, [word 0, word 5], word 0),
    (52, [word 255, word 16], word 15), (52, [word 7, word 7], word 0), (52, [word 5, word 255], word 5),
    (53, [word (modulus - 1), word 2], word (2 ^ 255 - 1)), (53, [word (modulus - 1), word (modulus - 1)], word 1),
    (54, [word (modulus - 1), word 2], word 1), (54, [word (modulus - 2), word (modulus - 1)], word (modulus - 2)),
    (55, [word (modulus - 7), word 2], word (modulus - 3)), (55, [word 7, word (modulus - 2)], word (modulus - 3)),
    (55, [word (modulus - 7), word (modulus - 2)], word 3), (55, [word (modulus - 128), word 1], word (modulus - 128)),
    (55, [word 127, word (modulus - 1)], word (modulus - 127)), (55, [word (modulus - 128), word 2], word (modulus - 64)),
    (55, [word (modulus - 1), word 2], word 0),
    (56, [word (modulus - 7), word 2], word (modulus - 1)), (56, [word 7, word (modulus - 2)], word 1),
    (56, [word (modulus - 7), word (modulus - 2)], word (modulus - 1)),
    (56, [word (modulus - 128), word (modulus - 1)], word 0), (56, [word (modulus - 128), word 3], word (modulus - 2)),
    (56, [word 127, word (modulus - 128)], word 127),
    (57, [word (2 ^ 255), word 1], word (2 ^ 255)), (57, [word (2 ^ 255), word 2], word (modulus - 2 ^ 254)),
    (57, [word (modulus - 7), word 2], word (modulus - 3)), (57, [word (2 ^ 255 - 1), word (modulus - 1)], word (2 ^ 255 + 1)),
    (58, [word (2 ^ 255), word (modulus - 1)], word 0), (58, [word (modulus - 7), word 2], word (modulus - 1)),
    (58, [word (2 ^ 255), word 3], word (modulus - 2)),
    -- Their compound forms, checked after the setter.
    (59, [word 200, word 3], word 66), (60, [word 200, word 3], word 2),
    (61, [word (modulus - 128), word 2], word (modulus - 64)), (61, [word (modulus - 7), word 2], word (modulus - 3)),
    (62, [word (modulus - 7), word 2], word (modulus - 1)), (62, [word (modulus - 128), word (modulus - 1)], word 0),
    (63, [word (2 ^ 255), word 2], word (modulus - 2 ^ 254)), (64, [word (modulus - 1), word 10], word 5),
    (65, [word (modulus - 6), word 3], word (modulus - 2)),
    -- Literals at the twelve types: the range edges as their words, and literal operands.
    (66, [], word 255), (67, [], word (modulus - 1)), (68, [], word 127), (69, [], word (2 ^ 255 - 1)),
    (70, [], word 0), (71, [word 254], word 255), (72, [word (2 ^ 255 - 2)], word (2 ^ 255 - 1)),
    (73, [word (modulus - 1)], boolean true), (73, [word 100], boolean false),
    (74, [word 0], boolean true), (74, [word 1], boolean false),
    (75, [word 127], word 254), (76, [word (modulus - 7)], word (modulus - 3)),
    (77, [word (modulus - 1)], word 5),
    -- A deferred operator takes the literal's later type.
    (78, [], word 3), (79, [], word 3),
    -- A literal key and element of a mapping.
    (80, [], word 200), (81, [word 9], word 127), (82, [word 0x1234], word 0x34),
    -- Unary minus: a negated literal folds into the literal, through groups and repeated.
    (84, [], word (modulus - 128)), (85, [], word (modulus - 128)),
    (86, [], word (modulus - 128)), (87, [], word 5),
    (88, [], word (2 ^ 255)), (89, [], word 0),
    -- A negative Word literal wraps, and so does one that takes the return's type.
    (90, [], word (modulus - 1)), (91, [], word (modulus - 1)),
    -- `-x` reads as checked `0 - x` on the twelve types and wraps on Word.
    (92, [word 5], word (modulus - 5)), (92, [word (modulus - 7)], word 7),
    (92, [word 0], word 0), (92, [word 127], word (modulus - 127)),
    (93, [word 0], word 0),
    (94, [word 1], word (modulus - 1)), (94, [word (modulus - 1)], word 1),
    (94, [word (2 ^ 255 - 1)], word (2 ^ 255 + 1)),
    (95, [word 0], word 0),
    (96, [word 1], word (modulus - 1)), (96, [word 0], word 0),
    (96, [word (2 ^ 255)], word (2 ^ 255)),
    -- A negated literal as an operand, in a compound assignment and in a comparison.
    (97, [word 5], word 4), (97, [word 0], word (modulus - 1)),
    (98, [word 3], word (modulus - 6)), (98, [word (2 ^ 254)], word (2 ^ 255)),
    (99, [word 5], word 0), (99, [word 127], word 122),
    (100, [word 0], word 1), (100, [word (modulus - 1)], word 0),
    -- A nested negation of a variable is `0 - (0 - x)`.
    (101, [word 5], word 5), (101, [word (modulus - 127)], word (modulus - 127)),
    (102, [word 5], word 5),
    -- In an unchecked block `-w` on Word wraps.
    (103, [word 1], word (modulus - 1)),
    (104, [word (modulus - 128)], boolean true), (104, [word 0], boolean false),
    (104, [word (modulus - 100)], boolean false),
    (105, [], word (modulus - 128))]
  let panicCases : List (Nat × List Value) := [
    (24, [word 200, word 56]), (25, [word 3, word 5]), (26, [word 65536, word 65536]),
    (27, [word (modulus - 1), word 1]), (28, [word (2 ^ 128), word (2 ^ 128)]),
    (29, [word 127, word 1]), (29, [word (modulus - 128), word (modulus - 1)]),
    (30, [word (modulus - 128), word 1]), (30, [word 0, word (modulus - 128)]),
    (31, [word (modulus - 128), word (modulus - 1)]), (32, [word (2 ^ 255), word 1]),
    (33, [word (modulus - 1), word (2 ^ 255)]),
    -- One past each edge of the compound forms: `Panic(0x11)` after the setter.
    (34, [word 200, word 56]), (35, [word 5, word 6]), (36, [word 16, word 16]),
    (37, [word (modulus - 1), word 1]), (38, [word 0, word 1]), (39, [word (2 ^ 128), word (2 ^ 128)]),
    (40, [word 127, word 1]), (40, [word (modulus - 100), word (modulus - 29)]),
    (41, [word 0, word (modulus - 128)]), (41, [word (modulus - 128), word 1]),
    (42, [word (modulus - 128), word (modulus - 1)]), (42, [word 64, word 2]),
    (43, [word (2 ^ 255 - 1), word 1]), (43, [word (2 ^ 255), word (modulus - 1)]),
    (44, [word 0, word (2 ^ 255)]), (44, [word (2 ^ 255), word 1]),
    (45, [word (2 ^ 255), word (modulus - 1)]), (45, [word (2 ^ 127), word (2 ^ 128)]),
    (49, [word 200, word 56]),
    -- `MIN / -1` leaves the range; `MIN % -1` above does not.
    (55, [word (modulus - 128), word (modulus - 1)]), (57, [word (2 ^ 255), word (modulus - 1)]),
    (61, [word (modulus - 128), word (modulus - 1)]), (63, [word (2 ^ 255), word (modulus - 1)]),
    (65, [word (modulus - 128), word (modulus - 1)]),
    -- Checked arithmetic with a literal operand, and a deferred `+` at `uint8` past its range.
    (71, [word 255]), (72, [word (2 ^ 255 - 1)]), (75, [word 128]), (83, []),
    -- `-x` panics for MIN and for any nonzero unsigned value, as do negated-literal operands
    -- leaving the range and the inner negation of `- -MIN`.
    (92, [word (modulus - 128)]), (93, [word 5]), (93, [word 255]),
    (94, [word (2 ^ 255)]), (95, [word 1]), (95, [word (modulus - 1)]),
    (97, [word (modulus - 128)]), (98, [word (2 ^ 254 + 1)]),
    (99, [word (modulus - 124)]), (100, [word (2 ^ 255 - 1)]),
    (101, [word (modulus - 128)])]
  -- A zero divisor panics with `Panic(0x12)`, `MIN / 0` too.
  let zeroCases : List (Nat × List Value) := [
    (51, [word 7, word 0]), (52, [word 7, word 0]), (53, [word 1, word 0]), (54, [word (modulus - 1), word 0]),
    (55, [word 5, word 0]), (55, [word (modulus - 128), word 0]), (56, [word 5, word 0]),
    (57, [word 1, word 0]), (58, [word (2 ^ 255), word 0]),
    (59, [word 7, word 0]), (60, [word 7, word 0]), (61, [word 5, word 0]), (62, [word 5, word 0]),
    (63, [word (2 ^ 255), word 0]), (64, [word 1, word 0]), (65, [word 1, word 0])]
  for (index, arguments, expected) in cases do
    let completed ← execute session (← key index) arguments
    require (completed.value == expected)
      s!"{names[index]?} on {reprStr arguments} gave {reprStr completed.value}"
    session := completed.session
  for (index, arguments) in panicCases do
    session ← panics session (← key index) arguments SourceCorePanics.arithmetic
      s!"{names[index]?} on {reprStr arguments}"
  for (index, arguments) in zeroCases do
    session ← panics session (← key index) arguments SourceCorePanics.divisionByZero
      s!"{names[index]?} on {reprStr arguments}"
  -- An absent operand fails with the compound assignment's own diagnostic.
  let uint8 ← match TypeSystem.FixedInteger.ofName? "uint8" with
    | some type => pure type | none => throw (IO.userError "uint8 missing")
  discard <| invalidOperands session (← key 50) [word 1]
    (.invalidAssignmentOperands .add none (some (.fixed uint8))) "absentAdd8u"
  rejectedByInference "operands of different types"
    ["function bad(x: uint8, y: uint16) returns (bool) { return x == y; }"]
  -- One past each type's greatest value is rejected, naming the type.
  rejectedOutOfRange "256 at uint8" "uint8" 256 ["function bad() returns (uint8) { return 256; }"]
  rejectedOutOfRange "2^256 at uint256" "uint256" 115792089237316195423570985008687907853269984665640564039457584007913129639936
    ["function bad() returns (uint256) { return 115792089237316195423570985008687907853269984665640564039457584007913129639936; }"]
  rejectedOutOfRange "128 at int8" "int8" 128 ["function bad() returns (int8) { return 128; }"]
  rejectedOutOfRange "2^255 at int256" "int256" 57896044618658097711785492504343953926634992332820282019728792003956564819968
    ["function bad() returns (int256) { return 57896044618658097711785492504343953926634992332820282019728792003956564819968; }"]
  rejectedOutOfRange "an operand of 256 at uint8" "uint8" 256
    ["function bad(x: uint8) returns (uint8) { return x + 256; }"]
  -- A negated literal's range is checked with its sign, and the diagnostic names the negative value.
  rejectedOutOfRange "-129 at int8" "int8" (-129) ["function bad() returns (int8) { return -129; }"]
  rejectedOutOfRange "-2^255 - 1 at int256" "int256" (-57896044618658097711785492504343953926634992332820282019728792003956564819969)
    ["function bad() returns (int256) { return -57896044618658097711785492504343953926634992332820282019728792003956564819969; }"]
  rejectedOutOfRange "-1 at uint8" "uint8" (-1) ["function bad() returns (uint8) { return -1; }"]
  rejectedOutOfRange "-1 at uint256" "uint256" (-1) ["function bad() returns (uint256) { return -1; }"]
  rejectedOutOfRange "an operand of -129 at int8" "int8" (-129)
    ["function bad(x: int8) returns (int8) { return x + -129; }"]
  -- `-e` reads as `0 - e`: a declared type has no builtin `Int` for the `0`, so it is rejected
  -- even with `Sub`. In a block `-x` is unchecked, which wraps on the twelve types (`runUnchecked`).
  rejectedByInference "unary minus on a declared type"
    ["enum Token { Token(Word) }", "trait Sub<T> {", "  function sub(left: T, right: T) returns (T);", "}",
     "impl Sub<Token> {", "  function sub(left: Token, right: Token) returns (Token) {", "    return left;", "  }", "}",
     "function bad(t: Token) returns (Token) { return -t; }"]
  rejectedByInference "unary minus on Bool" ["function bad(b: Bool) returns (Bool) { return -b; }"]
  IO.println "SOURCE_CORE_FIXED_OPERATORS_PASS: == != & | ^ < > <= >= ~ and checked + - * / % on signed and unsigned fixed-width types, signed orderings comparing negative words, ~ keeping the low bits on narrower unsigned types, checked arithmetic and checked += -= *= /= %= panicking with 0x11 outside the range (MIN / -1 among them, MIN % -1 not), / % /= %= panicking with 0x12 on a zero divisor and rounding toward zero, an absent += operand failing with its own diagnostic, &= |= ^= as Word's, with canonical results, and mixed operand types, literals at their range edges and as operands, deferred operators and mapping elements, one past each range rejected naming the type, negated literals folded through groups and repeated with their range checked by sign, -x as checked 0 - x panicking for MIN and nonzero unsigned values and wrapping on Word, negated-literal operands and compound forms, unary minus rejected on declared types and Bool"
  runDefaulting
  runUnchecked
  runShifts
  runCompoundShifts
  runBitNotAssignments
  runConversions
  runTypedef
  runUint256Patterns
  runBoolPatterns
  runBareNamePatterns
  runConstructorNames
  runMatchCoverage
  runCallLookup
  runLeadingDotBooleans
  runNonFinalReturns
  runUpstreamFixtures
  runUpstreamArrayFixtures
  runArrayElementCases

end Tests.SourceCoreFixedIntegerOperators
end

section
-- leanmerge: from Solcore.Test.SourceCoreExecution
#check_failure Solcore.Frontend.SourceCoreExecution.Options.backendPreference
#check_failure Solcore.Frontend.SourceCoreExecution.Compiled.mk
#check_failure Solcore.Frontend.SourceCoreExecution.Artifact.mk
#check_failure Solcore.Frontend.SourceCoreExecution.Session.payload
#check_failure Solcore.Frontend.SourceCoreExecution.Checkpoint.payload
#check_failure Solcore.Frontend.SourceCoreExecution.Value.closure
#check_failure Solcore.Frontend.SourceCoreExecution.Value.cellRef
#check_failure Solcore.Frontend.SourceCoreExecution.Authentication.mk

/-! The same public value, artifact, session and checkpoint types execute data,
recursive calls and returned native functions. Closures capture by value: every
call of a retained closure starts again from its creation-time captures. The
empty compilation has no callable code. All setup is cached before opening an
ownership domain. -/
set_option autoImplicit false
namespace Tests.SourceCoreExecution
open Solcore Solcore.Frontend SourceCoreExecution

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def word (n : Nat) : Value := .word (Core.Word.ofNatModulo n)
private def handle : Value → IO Handle
  | .function handle => pure handle
  | _ => throw (IO.userError "public function did not export an owned handle")
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := "pragma solcore;\n" ++ String.intercalate "\n" [
    "function make(seed: Word) returns (function(Word) returns (Word)) { return lam(step: Word) { seed += step; return seed; }; }",
    "function use(f: function(Word) returns (Word), step: Word) returns (Word) { return f(step); }",
    "function recurse(n: Word) returns (Word) { return n == 0 ? 31 : recurse(n - 1); }",
    "function local(flag: Bool) returns (Word, Bool) { let id = lam(value) { return value; }; return (id(7), id(flag)); }",
    "function mappingEcho(value: mapping(Word => Word)) returns (mapping(Word => Word)) { return value; }",
    "function spin() returns (Word) { while (true) {} return 0; }",
    "function main() returns (Word) { return 55; }",
    "function uninitialized() returns (Word) { let absent: Word; return absent; }",
    "function marked(comptime value: Word) returns (Word) { return value; }",
    "function builtinUse(f: function(Word) returns (integer)) returns (integer) { return f(9); }",
    "function namedUse(f: function(Word) returns (Word)) returns (Word) { return f(4); }",
    "function mixedUse(first: function(Word) returns (Word), step: Word, table: mapping(Word => Word), convert: function(Word) returns (integer), again: function(Word) returns (Word)) returns (integer) { return convert(first(step) + step + table[step] + again(step + 1)); }",
    "enum NestedFunctions { Hold(function(Word) returns (Word), function(Word) returns (integer)) }",
    "function nestedUse(bundle: (NestedFunctions, (mapping(Word => (function(Word) returns (Word), Word)), function(Word) returns (integer)))) returns (integer) { match (bundle) { case (.Hold(first, convert), (table, last)) { match (table[3]) { case (again, bonus) { return integerAdd(convert(first(3) + bonus + again(4)), last(2)); } default { return 999; } } } default { return 998; } } }",
    "function closureNestedUse(bundle: (NestedFunctions, (mapping(Word => (function(Word) returns (Word), function(Word) returns (Word))), function(Word) returns (integer)))) returns (integer) { match (bundle) { case (.Hold(first, convert), (table, last)) { match (table[3]) { case (again, namedFunction) { return integerAdd(convert(first(2) + again(6)), last(namedFunction(0))); } default { return 997; } } } default { return 996; } } }",
    "function distinctClosureUse(bundle: (function(Word) returns (Word), mapping(Word => (function(Word) returns (Word), function(Word) returns (Word))))) returns (Word) { match (bundle) { case (first, table) { match (table[3]) { case (again, other) { return first(2) + again(6) + other(7); } default { return 995; } } } default { return 994; } } }",
    "function integratedHistoryUse(bundle: (NestedFunctions, (mapping(Word => (function(Word) returns (Word), function(Word) returns (Word))), function(Word) returns (Word)))) returns (integer) { match (bundle) { case (.Hold(first, convert), (table, namedFunction)) { match (table[3]) { case (again, other) { return convert(first(2) + again(6) + other(7) + namedFunction(3)); } default { return 993; } } } default { return 992; } } }",
    "function makePair(firstSeed: Word, secondSeed: Word) returns (function(Word) returns (Word), function(Word) returns (Word)) { return (lam(step: Word) { firstSeed += step; return firstSeed; }, lam(step: Word) { secondSeed += step; return secondSeed; }); }",
    "function touchThenFail(f: function(Word) returns (Word), step: Word) returns (Word) { f(step); let absent: Word; return absent; }",
    "export {recurse};"
  ]}] }
private def seed (program : CheckedProgram) (name : String) : IO Seed :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure (SourceCoreCompiler.Seed.declaration signature.id)
  | _ => throw (IO.userError s!"single public execution fixture missing {name}")
private def execute {artifact : Artifact} (session : Session artifact) (key : Key) (arguments : List Value) :
    IO (Completion artifact) := do
  let executed ← session.runWithReceipt key arguments {executionFuel := 300000}
  match executed.val with
  | .ok (.succeeded result) => pure result
  | .ok (.exportError error _) => throw (IO.userError s!"public export: {reprStr error}")
  | .ok (.failed reason _) => throw (IO.userError s!"public language failure: {reprStr reason}")
  | .ok (.outOfFuel _) => throw (IO.userError "public execution exhausted")
  | .error error => throw (IO.userError s!"public invocation: {reprStr error}")
private def boot (artifact : Artifact) : IO (Session artifact) := do
  let fresh ← artifact.bootstrapWithReceipt
  let bootstrap := fresh.val
  match bootstrap.resume 300000 with
  | .ready session => pure session
  | .error error => throw (IO.userError s!"public bootstrap: {reprStr error}")
  | .outOfFuel _ => throw (IO.userError "public bootstrap exhausted")

example (compiled : Compiled) :
    SourceCompilationPlan.validateExecutablePlanEvidence compiled.program compiled.plan = .ok () := compiled.plan_validated
example {raw : Workspace.RawWorkspace} {seeds : List Seed} {options : Options} {compiled : Compiled}
    (accepted : compile raw seeds options = .ok compiled) :
    checkProgram raw options.checkingFuel = .ok compiled.program := compile_checked_source accepted
example {artifact : Artifact} (completion : Completion artifact) :
    completion.session.Authenticates completion.boundaryFuel completion.sourceType completion.value := completion.typed
example {raw : Workspace.RawWorkspace} {options : Options} {compiled : Compiled}
    (accepted : compileEntry raw options = .ok compiled) :
    checkProgram raw options.checkingFuel = .ok compiled.program := compileEntry_checked_source accepted
example {raw : Workspace.RawWorkspace} {options : Options} {compiled : StaticWordProgram}
    (accepted : compileStaticWord raw options = .ok compiled) :
    checkProgram raw options.checkingFuel = .ok compiled.compiled.program := compileStaticWord_checked_source accepted

/-- solcore-rs #120's programs, a repeated call, a loop-carried capture and
upstream's `control-flow-capture-identity` fixture without its pragma, std
wrappers and inline Yul: a closure keeps the values captured at its creation,
and each call starts again from them. -/
private def captureWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := "pragma solcore;\n" ++ String.intercalate "\n" [
    "function issue120First() returns (Word) { let x: Word = 40; let f = lam(step: Word) { return x + step; }; x = 99; return f(2); }",
    "function issue120Second() returns (Word) { let x: Word = 41; let f = lam() { x = 42; return x; }; let result: Word = f(); return result + x; }",
    "function repeated() returns (Word) { let x: Word = 0; let f = lam() { x = x + 1; return x; }; let a: Word = f(); let b: Word = f(); return a * 10 + b + x * 100; }",
    "function loopCarried(count: Word) returns (Word) { let i: Word = 0; let acc: Word = 0; while (i < count) { let f = lam() { let w: Word = i * 10; i = i + 100; return w + acc; }; acc = f(); i = i + 1; } return acc + i * 1000; }",
    "function branch(flag: Bool, value: Word) returns (Word) { let x: Word = value; if (flag) { let first = lam() { let result: Word; result = x; return result; }; x = x + 7; let second = lam() { let result: Word; result = x; return result; }; return first() + second(); } return 0; }",
    "function loop(count: Word, value: Word) returns (Word) { let x: Word = value; let total: Word = 0; for (let i: Word = 0; i < count; i = i + 1) { let first = lam() { let result: Word; result = x; return result; }; x = x + 7; let second = lam() { let result: Word; result = x; return result; }; total = first() + second(); } return total; }",
    "function nested(flag: Bool, count: Word, value: Word) returns (Word) { let x: Word = value; let total: Word = 0; if (flag) { for (let i: Word = 0; i < count; i = i + 1) { let first = lam() { let result: Word; result = x; return result; }; x = x + 7; { let second = lam() { let result: Word; result = x; return result; }; x = x + 7; if (flag) { let third = lam() { let result: Word; result = x; return result; }; total = first() + second() + third(); } } } } return total; }"
  ]}] }

private def runCaptures : IO Unit := do
  let program ← get "capture check" (checkProgram captureWorkspace)
  let seeds ← ["issue120First", "issue120Second", "repeated", "loopCarried", "branch", "loop", "nested"].mapM (seed program)
  let compiled ← get "capture compilation"
    (compile captureWorkspace seeds {specializationBudget := 256, compilationFuel := 1000})
  let key (index : Nat) : IO Key := match compiled.keys[index]? with
    | some key => pure key | none => throw (IO.userError "capture root missing")
  let initial ← boot (← compiled.open)
  let first ← execute initial (← key 0) []
  require (first.value == word 42) "a later outer assignment reached the closure"
  let second ← execute first.session (← key 1) []
  require (second.value == word 83) "a closure assignment reached the enclosing scope"
  let repeated ← execute second.session (← key 2) []
  require (repeated.value == word 11) "a closure call did not restart from the captured values"
  let loopNone ← execute repeated.session (← key 3) [word 0]
  let loopFour ← execute loopNone.session (← key 3) [word 4]
  require (loopNone.value == word 0 && loopFour.value == word 4060)
    "a closure created in a loop body lost a loop-carried capture"
  let mut session := loopFour.session
  let yes : Value := .bool true
  let no : Value := .bool false
  let cases : List (Nat × List Value × Nat) :=
    [(4, [yes, word 3], 13), (4, [yes, word 0], 7), (4, [no, word 3], 0),
     (5, [word 0, word 3], 0), (5, [word 1, word 3], 13), (5, [word 2, word 3], 27),
     (6, [yes, word 1, word 3], 30), (6, [yes, word 2, word 3], 72),
     (6, [no, word 1, word 3], 0), (6, [yes, word 0, word 3], 0)]
  for (index, arguments, expected) in cases do
    let completed ← execute session (← key index) arguments
    require (completed.value == word expected) s!"capture identity case {index} gave {reprStr completed.value}"
    session := completed.session

/-- `Panic(code)`: the call fails with the code, which the session decodes. -/
private def panics {artifact : Artifact} (session : Session artifact) (key : Key) (arguments : List Value)
    (code : UInt8) (label : String) : IO (Session artifact) := do
  let executed ← session.runWithReceipt key arguments {executionFuel := 300000}
  match executed.val with
  | .ok (.failed reason next) =>
      require (SourceCorePanics.code? reason == some code) s!"{label} failed with {reprStr reason}"
      match session.diagnostic key reason with
      | .ok (some diagnostic) =>
          require (decide (diagnostic.error = .panic code)) s!"{label} decoded {reprStr diagnostic.error}"
      | other => throw (IO.userError s!"{label} decoded {reprStr other}")
      pure next
  | .ok (.succeeded result) => throw (IO.userError s!"{label} gave {reprStr result.value}")
  | .ok _ => throw (IO.userError s!"{label} did not fail")
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")

/-- Upstream's `closure-parameters` fixture (`tests/e2e/closure-parameters/main.sol` at
e2eef194): its top-level helpers and the 23 public functions that need no contract storage and no
inline assembly, as upstream wrote them, with the contract's methods as functions. They include
the storage-free factory cases at this pin, `runtimeFactory`, `computedFactory` and
`unusedComputedFactory`. The fixture's other 12 calls read or write the contract's `count`,
`incremented` or `locked`, or run `assemblyCapture`'s inline Yul, which the native pipeline does
not have. -/
private def closureParameterWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := "pragma solcore;\n" ++ String.intercalate "\n" [
    "function makeAdder(value: uint256) returns (function (uint256) returns (uint256)) {",
    "    return lam (other: uint256) -> uint256 {",
    "        return value + other;",
    "    };",
    "}",
    "function makeComputedAdder(value: uint256) returns (function (uint256) returns (uint256)) {",
    "    let incremented = value + uint256(1);",
    "    return lam (other: uint256) -> uint256 {",
    "        return incremented + other;",
    "    };",
    "}",
    "function makeCheckedConstant(value: uint256) returns (function () returns (uint256)) {",
    "    let unused = value + uint256(1);",
    "    return lam () -> uint256 {",
    "        return uint256(7);",
    "    };",
    "}",
    "function twice(f: function (uint256) returns (uint256), x: uint256) returns (uint256) {",
    "    return f(f(x));",
    "}",
    "function forward(f: function (uint256) returns (uint256), x: uint256) returns (uint256) {",
    "    return twice(f, x);",
    "}",
    "function repeat(f: function (uint256) returns (uint256), x: uint256, n: uint256) returns (uint256) {",
    "    if (n == uint256(0)) {",
    "        return x;",
    "    }",
    "    return repeat(f, f(x), n - uint256(1));",
    "}",
    "function increment(x: uint256) returns (uint256) {",
    "    return x + uint256(1);",
    "}",
    "function run(f: function () returns (uint256)) returns (uint256) {",
    "    return f();",
    "}",
    "function apply2(f: function (uint256, uint256) returns (uint256), x: uint256, y: uint256) returns (uint256) {",
    "    return f(x, y);",
    "}",
    "function applyWord(f: function (word) returns (word), x: word) returns (word) {",
    "    return f(x);",
    "}",
    "function applyGeneric<a>(f: function (a) returns (a), x: a) returns (a) {",
    "    return f(x);",
    "}",
    "function forwardValue<a>(value: a) returns (a) {",
    "    return value;",
    "}",
    "function inferred() returns (uint256) {",
    "    let f = lam (x: word) -> word {",
    "        return x;",
    "    };",
    "    return uint256(applyWord(f, 42));",
    "}",
    "function inferredCaptured(amount: uint256, x: uint256) returns (uint256) {",
    "    let f = lam (v: uint256) -> uint256 {",
    "        return v + amount;",
    "    };",
    "    amount = uint256(99);",
    "    return forward(f, x);",
    "}",
    "function inferredAlias(amount: uint256, x: uint256) returns (uint256) {",
    "    let f = lam (v: uint256) -> uint256 {",
    "        return v + amount;",
    "    };",
    "    let g = f;",
    "    return twice(g, x);",
    "}",
    "function inferredGeneric(amount: uint256, x: uint256) returns (uint256) {",
    "    let f = lam (v: uint256) -> uint256 {",
    "        return v + amount;",
    "    };",
    "    return applyGeneric(f, x);",
    "}",
    "function inferredGenericResult(x: uint256) returns (uint256) {",
    "    let f = lam (y: uint256) -> uint256 {",
    "        return y + x;",
    "    };",
    "    let callback: function (uint256) returns (uint256) = forwardValue(f);",
    "    return callback(uint256(2));",
    "}",
    "function inferredIndirectResult(x: uint256) returns (uint256) {",
    "    let f = lam (y: uint256) -> uint256 {",
    "        return y + x;",
    "    };",
    "    let factory = lam () {",
    "        return f;",
    "    };",
    "    let callback: function (uint256) returns (uint256) = factory();",
    "    return callback(uint256(2));",
    "}",
    "function inferredNullary(x: uint256) returns (uint256) {",
    "    let f = lam () -> uint256 {",
    "        return x + uint256(2);",
    "    };",
    "    return run(f);",
    "}",
    "function inferredMultipleArgs(amount: uint256, x: uint256, y: uint256) returns (uint256) {",
    "    let f = lam (a: uint256, b: uint256) -> uint256 {",
    "        return a + b + amount;",
    "    };",
    "    return apply2(f, x, y);",
    "}",
    "function shifted(x: uint256) returns (uint256) {",
    "    let f = makeAdder(uint256(10));",
    "    let base = f(uint256(32));",
    "    return base + x;",
    "}",
    "function fixed() returns (uint256) {",
    "    return twice(lam (v: uint256) -> uint256 {",
    "            return v + uint256(10);",
    "        }, uint256(22));",
    "}",
    "function addTwenty(x: uint256) returns (uint256) {",
    "    return twice(lam (v: uint256) -> uint256 {",
    "            return v + uint256(10);",
    "        }, x);",
    "}",
    "function factory(x: uint256) returns (uint256) {",
    "    return twice(makeAdder(uint256(10)), x);",
    "}",
    "function runtimeFactory(step: uint256, x: uint256) returns (uint256) {",
    "    let f = makeAdder(step);",
    "    return f(x);",
    "}",
    "function computedFactory(step: uint256, x: uint256) returns (uint256) {",
    "    let f = makeComputedAdder(step);",
    "    return f(x);",
    "}",
    "function unusedComputedFactory(step: uint256) returns (uint256) {",
    "    let unused = makeCheckedConstant(step);",
    "    return uint256(1);",
    "}",
    "function shadowed(x: uint256) returns (uint256) {",
    "    let v = uint256(99);",
    "    return twice(lam (v: uint256) -> uint256 {",
    "            return v + uint256(1);",
    "        }, x);",
    "}",
    "function captured(amount: uint256, x: uint256) returns (uint256) {",
    "    return forward(lam (v: uint256) -> uint256 {",
    "            return v + amount;",
    "        }, x);",
    "}",
    "function capturedFieldName(count: uint256, x: uint256) returns (uint256) {",
    "    return twice(lam (v: uint256) -> uint256 {",
    "            return v + count;",
    "        }, x);",
    "}",
    "function capturedBeforeAssignment(x: uint256) returns (uint256) {",
    "    let f: function (uint256) returns (uint256) = lam (v: uint256) -> uint256 {",
    "        return v + x;",
    "    };",
    "    x = uint256(99);",
    "    return twice(f, uint256(0));",
    "}",
    "function named(x: uint256) returns (uint256) {",
    "    return twice(increment, x);",
    "}",
    "function recursive(amount: uint256, x: uint256, n: uint256) returns (uint256) {",
    "    return repeat(lam (v: uint256) -> uint256 {",
    "            return v + amount;",
    "        }, x, n);",
    "}",
    "function nullary(x: uint256) returns (uint256) {",
    "    return run(lam () -> uint256 {",
    "            return x + uint256(2);",
    "        });",
    "}",
    "function multipleArgs(amount: uint256, x: uint256, y: uint256) returns (uint256) {",
    "    return apply2(lam (a: uint256, b: uint256) -> uint256 {",
    "            return a + b + amount;",
    "        }, x, y);",
    "}"
  ]}] }

private def closureParameterNames : List String := [
  "inferred", "inferredCaptured", "inferredAlias", "inferredGeneric", "inferredGenericResult",
  "inferredIndirectResult", "inferredNullary", "inferredMultipleArgs", "shifted", "fixed",
  "addTwenty", "factory", "runtimeFactory", "computedFactory", "unusedComputedFactory",
  "shadowed", "captured", "capturedFieldName", "capturedBeforeAssignment", "named", "recursive",
  "nullary", "multipleArgs"]

/-- Lean's own storage-free analogs of the factory cases that upstream's bf7114a8 and ad1f49cf
added at this pin, which use contract storage. A memory array that the factory writes stands for
the storage (`factoryEffectOrder`, `unusedFactoryEffects`, `discardedFactoryEffects`,
`reassignedFactoryEffects`), and a caller's local or an expired block local shadows a name the
closure uses (`factoryLocalShadows`, `factoryCallerShadows`, `factoryExpiredShadow`). The pinned
driver gives these values too, on Sonatina O0 and O2 and on Yul. -/
private def closureFactoryWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := "pragma solcore;\n" ++ String.intercalate "\n" [
    "function makeAdder(value: uint256) returns (function (uint256) returns (uint256)) {",
    "    return lam (other: uint256) -> uint256 {",
    "        return value + other;",
    "    };",
    "}",
    "function makeComputedAdder(value: uint256) returns (function (uint256) returns (uint256)) {",
    "    let incremented = value + uint256(1);",
    "    return lam (other: uint256) -> uint256 {",
    "        return incremented + other;",
    "    };",
    "}",
    "function increment(x: uint256) returns (uint256) {",
    "    return x + uint256(1);",
    "}",
    "function makeCountedAdder(step: uint256, c: uint256[]) returns (function (uint256) returns (uint256)) {",
    "    c[0] = c[0] + uint256(1);",
    "    let first = step + c[0];",
    "    c[0] = c[0] + uint256(1);",
    "    let second = step + c[0];",
    "    return lam (other: uint256) -> uint256 {",
    "        return first + second + other;",
    "    };",
    "}",
    "function makeAdderWithFunction(step: uint256) returns (function (uint256) returns (uint256)) {",
    "    let incremented = step + uint256(1);",
    "    return lam (other: uint256) -> uint256 {",
    "        return increment(incremented) + other;",
    "    };",
    "}",
    "function makeAdderWithExpiredShadow(step: uint256) returns (function (uint256) returns (uint256)) {",
    "    {",
    "        let increment: bool = true;",
    "    }",
    "    let incremented = step + uint256(1);",
    "    return lam (other: uint256) -> uint256 {",
    "        return increment(incremented) + other;",
    "    };",
    "}",
    "function factoryLocalShadows(step: uint256) returns (uint256) {",
    "    let incremented = uint256(100);",
    "    let f = makeComputedAdder(step);",
    "    return f(uint256(1));",
    "}",
    "function factoryCallerShadows(step: uint256) returns (uint256) {",
    "    let increment = uint256(100);",
    "    let f = makeAdderWithFunction(step);",
    "    return f(uint256(1));",
    "}",
    "function factoryExpiredShadow(step: uint256) returns (uint256) {",
    "    let f = makeAdderWithExpiredShadow(step);",
    "    return f(uint256(1));",
    "}",
    "function factoryEffectOrder(step: uint256) returns (uint256) {",
    "    let c: uint256[] = new uint256[](1);",
    "    let f = makeCountedAdder(step, c);",
    "    c[0] = c[0] + uint256(10);",
    "    return f(uint256(0)) + f(uint256(0)) + c[0];",
    "}",
    "function unusedFactoryEffects(step: uint256) returns (uint256) {",
    "    let c: uint256[] = new uint256[](1);",
    "    let unused = makeCountedAdder(step, c);",
    "    return c[0];",
    "}",
    "function discardedFactoryEffects(step: uint256) returns (uint256) {",
    "    let c: uint256[] = new uint256[](1);",
    "    makeCountedAdder(step, c);",
    "    return c[0];",
    "}",
    "function reassignedFactoryEffects(step: uint256) returns (uint256) {",
    "    let c: uint256[] = new uint256[](1);",
    "    let f = makeAdder(step);",
    "    f = makeCountedAdder(step, c);",
    "    return f(uint256(0)) + c[0];",
    "}"
  ]}] }

/-- Row 7, closure factories: closure-parameters' cases that the native pipeline can run, each
value and each `Panic(0x11)` the fixture's, among them a factory's checked addition, which panics
when the factory runs even if its closure is never called; then the analogs, in which a factory's
writes happen when it runs, in order, whether its closure is used, discarded or replaced, and a
closure reads the factory's own bindings. -/
private def runClosureParameterFixtures : IO Unit := do
  let maximum := 2 ^ 256 - 1
  let program ← get "closure-parameters check" (checkProgram closureParameterWorkspace)
  let seeds ← closureParameterNames.mapM (seed program)
  let compiled ← get "closure-parameters compilation"
    (compile closureParameterWorkspace seeds {specializationBudget := 256, compilationFuel := 1000})
  let key (name : String) : IO Key := match closureParameterNames.findIdx? (· == name) with
    | some index => match compiled.keys[index]? with
      | some key => pure key
      | none => throw (IO.userError s!"closure-parameters root {name} missing")
    | none => throw (IO.userError s!"closure-parameters {name} unknown")
  let mut session ← boot (← compiled.open)
  let cases : List (String × List Value × Nat) := [
    ("inferred", [], 42), ("inferredCaptured", [word 10, word 22], 42),
    ("inferredCaptured", [word 7, word 3], 17), ("inferredAlias", [word 10, word 22], 42),
    ("inferredAlias", [word 7, word 3], 17), ("inferredGeneric", [word 10, word 32], 42),
    ("inferredGeneric", [word 7, word 3], 10), ("inferredGenericResult", [word 40], 42),
    ("inferredGenericResult", [word 3], 5), ("inferredIndirectResult", [word 40], 42),
    ("inferredIndirectResult", [word 3], 5), ("inferredNullary", [word 40], 42),
    ("inferredNullary", [word 3], 5), ("inferredMultipleArgs", [word 10, word 20, word 12], 42),
    ("inferredMultipleArgs", [word 3, word 4, word 5], 12), ("shifted", [word 0], 42),
    ("shifted", [word 8], 50), ("fixed", [], 42), ("addTwenty", [word 0], 20),
    ("addTwenty", [word 22], 42), ("factory", [word 22], 42),
    ("runtimeFactory", [word 5, word 37], 42), ("computedFactory", [word 4, word 37], 42),
    ("unusedComputedFactory", [word 4], 1), ("shadowed", [word 40], 42),
    ("captured", [word 10, word 22], 42), ("captured", [word 7, word 3], 17),
    ("capturedFieldName", [word 10, word 22], 42), ("capturedBeforeAssignment", [word 21], 42),
    ("named", [word 10], 12), ("recursive", [word 3, word 5, word 4], 17),
    ("recursive", [word 8, word 2, word 0], 2), ("nullary", [word 40], 42),
    ("multipleArgs", [word 10, word 20, word 12], 42)]
  for (name, arguments, expected) in cases do
    let completed ← execute session (← key name) arguments
    require (completed.value == word expected) s!"{name} on {reprStr arguments} gave {reprStr completed.value}"
    session := completed.session
  for (name, arguments) in ([("runtimeFactory", [word 1, word maximum]), ("computedFactory", [word maximum, word 0]), ("unusedComputedFactory", [word maximum])] : List (String × List Value)) do
    session ← panics session (← key name) arguments SourceCorePanics.arithmetic s!"{name} on {reprStr arguments}"
  let analogNames := ["factoryLocalShadows", "factoryCallerShadows", "factoryExpiredShadow", "factoryEffectOrder", "unusedFactoryEffects", "discardedFactoryEffects", "reassignedFactoryEffects"]
  let analogProgram ← get "closure factory analog check" (checkProgram closureFactoryWorkspace)
  let analogSeeds ← analogNames.mapM (seed analogProgram)
  let analogCompiled ← get "closure factory analog compilation"
    (compile closureFactoryWorkspace analogSeeds {specializationBudget := 256, compilationFuel := 1000})
  let mut analogSession ← boot (← analogCompiled.open)
  for (index, argument, expected) in ([(0, 4, 6), (1, 4, 7), (2, 4, 7), (3, 3, 30), (4, 3, 2), (5, 3, 2), (6, 3, 11)] : List (Nat × Nat × Nat)) do
    let analogKey ← match analogCompiled.keys[index]? with
      | some key => pure key
      | none => throw (IO.userError "closure factory analog root missing")
    let completed ← execute analogSession analogKey [word argument]
    require (completed.value == word expected)
      s!"{analogNames[index]!}({argument}) gave {reprStr completed.value}"
    analogSession := completed.session
  IO.println "SOURCE_CORE_CLOSURE_PARAMETERS_PASS: upstream's closure-parameters cases that need no contract storage and no inline assembly, as upstream wrote them, give the fixture's values and Panic(0x11), a closure factory's checked addition panicking when the factory runs, and Lean's storage-free analogs of its storage cases give the pinned driver's values: a factory's writes happen when it runs, in order, whether its closure is used, discarded or replaced, and its closure reads the factory's own bindings, not a caller's or an expired local's"

/-- Twelve data types that each double their argument for the next, then a thirteenth that holds
it: a finite program whose last instantiation, `E12<T>`, has 8192 nodes. Upstream's emitter lowers
it; Lean's catalog refuses it past `SourceCoreDataCatalog.maxTypeNodes` (row 6, step 2). -/
private def doublingWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" (["pragma solcore;", ""] ++
    (List.range 12).map (fun k => s!"enum E{k}<a> " ++ "{ " ++ s!"E{k}(E{k + 1}<(a, a)>)" ++ " }") ++
    ["enum E12<a> { E12(a) }", "function main(x: E0<word>) returns (word) {", "    return 0;", "}"]) }]
}

/-- Row 6's step 2: the catalog refuses a nominal instantiation past `maxTypeNodes`, upstream's
default `--pe-max-type-nodes`. -/
private def runLayoutBound : IO Unit := do
  let program ← get "doubling check" (checkProgram doublingWorkspace)
  match compile doublingWorkspace [← seed program "main"] with
  | .error (.compilation (.compilation (.compatible (.catalog (.catalog (.typeSizeExceeded id limit)))))) =>
      let named := (program.signatures.dataTypes.find? fun data => decide (data.id = id)).map (·.name)
      require (limit == SourceCoreDataCatalog.maxTypeNodes && named == some "E12")
        s!"the doubling program refused at {reprStr named} with {limit} nodes"
  | .error error => throw (IO.userError s!"the doubling program refused otherwise: {(reprStr error).take 400}")
  | .ok _ => throw (IO.userError "the doubling program compiled")
  IO.println "SOURCE_CORE_LAYOUT_BOUND_PASS: a finite program whose twelve data types each double their argument is refused once an instantiation passes upstream's default --pe-max-type-nodes, at the thirteenth"

/-- Upstream's layout fixtures (`crates/hull/tests/fixtures/layouts` at `e2eef194`), generated by
`gen_test.py` in the row 6 step 3 records: name, expectation, the type that a non-regular one names,
whether `main` takes a word, and the source. -/
private def layoutFixtures : List (String × String × String × Bool × String) := [
  ("finite_fixed_comptime", "unsupported-recursive", "Nest", false,
    String.intercalate "\n" [
      "pragma solcore;",
      "",
      "//~ layout: unsupported-recursive",
      "enum Box<a> {",
      "    Box(a)",
      "}",
      "enum Nest<a, b> {",
      "    Nil,",
      "    Next(a, Nest<comptime<word>, b>)",
      "}",
      "function main(x: Nest<word, bool>) returns (word) {",
      "    return 0;",
      "}"]),
  ("finite_permuted", "unsupported-recursive", "Nest", false,
    String.intercalate "\n" [
      "pragma solcore;",
      "",
      "//~ layout: unsupported-recursive",
      "enum Box<a> {",
      "    Box(a)",
      "}",
      "enum Nest<a, b> {",
      "    Nil,",
      "    Next(a, Nest<b, a>)",
      "}",
      "function main(x: Nest<word, bool>) returns (word) {",
      "    return 0;",
      "}"]),
  ("finite_regular", "unsupported-recursive", "Nest", false,
    String.intercalate "\n" [
      "pragma solcore;",
      "",
      "//~ layout: unsupported-recursive",
      "enum Box<a> {",
      "    Box(a)",
      "}",
      "enum Nest<a, b> {",
      "    Nil,",
      "    Next(a, Nest<a, b>)",
      "}",
      "function main(x: Nest<word, bool>) returns (word) {",
      "    return 0;",
      "}"]),
  ("finite_reset_box", "unsupported-recursive", "Nest", false,
    String.intercalate "\n" [
      "pragma solcore;",
      "",
      "//~ layout: unsupported-recursive",
      "enum Box<a> {",
      "    Box(a)",
      "}",
      "enum Nest<a, b> {",
      "    Nil,",
      "    Next(a, Nest<Box<b>, word>)",
      "}",
      "function main(x: Nest<word, bool>) returns (word) {",
      "    return 0;",
      "}"]),
  ("finite_reset_comptime", "unsupported-recursive", "Nest", false,
    String.intercalate "\n" [
      "pragma solcore;",
      "",
      "//~ layout: unsupported-recursive",
      "enum Box<a> {",
      "    Box(a)",
      "}",
      "enum Nest<a, b> {",
      "    Nil,",
      "    Next(a, Nest<comptime<b>, word>)",
      "}",
      "function main(x: Nest<word, bool>) returns (word) {",
      "    return 0;",
      "}"]),
  ("finite_unused_comptime", "finite", "Nest", false,
    String.intercalate "\n" [
      "pragma solcore;",
      "",
      "//~ layout: finite",
      "enum Box<a> {",
      "    Box(a)",
      "}",
      "enum Ignore<a> {",
      "    Ignore",
      "}",
      "enum Nest<a, b> {",
      "    Next(Ignore<Nest<comptime<a>, b>>)",
      "}",
      "function main(x: Nest<word, bool>) returns (word) {",
      "    return 0;",
      "}"]),
  ("finite_unused_growing", "finite", "Nest", false,
    String.intercalate "\n" [
      "pragma solcore;",
      "",
      "//~ layout: finite",
      "enum Box<a> {",
      "    Box(a)",
      "}",
      "enum Ignore<a> {",
      "    Ignore",
      "}",
      "enum Nest<a, b> {",
      "    Next(Ignore<Nest<Box<a>, b>>)",
      "}",
      "function main(x: Nest<word, bool>) returns (word) {",
      "    return 0;",
      "}"]),
  ("finite_wrapped_regular", "unsupported-recursive", "Nest", false,
    String.intercalate "\n" [
      "pragma solcore;",
      "",
      "//~ layout: unsupported-recursive",
      "enum Box<a> {",
      "    Box(a)",
      "}",
      "enum Nest<a, b> {",
      "    Nil,",
      "    Next(Box<Box<Nest<a, b>>>)",
      "}",
      "function main(x: Nest<word, bool>) returns (word) {",
      "    return 0;",
      "}"]),
  ("fixed_argument_unused", "finite", "Root", false,
    String.intercalate "\n" [
      "pragma solcore;",
      "",
      "//~ layout: finite",
      "enum Box<a> {",
      "    Box(a)",
      "}",
      "enum Ignore<a> {",
      "    Ignore",
      "}",
      "enum Grow<a> {",
      "    Stop,",
      "    Next(Grow<Box<a>>)",
      "}",
      "enum Root {",
      "    Root(Ignore<Grow<word>>)",
      "}",
      "function main(x: Root) returns (word) {",
      "    return 0;",
      "}"]),
  ("fixed_argument_used", "non-regular", "Root", false,
    String.intercalate "\n" [
      "pragma solcore;",
      "",
      "//~ layout: non-regular",
      "enum Box<a> {",
      "    Box(a)",
      "}",
      "enum Ignore<a> {",
      "    Ignore",
      "}",
      "enum Grow<a> {",
      "    Stop,",
      "    Next(Grow<Box<a>>)",
      "}",
      "enum Root {",
      "    Root(Box<Grow<word>>)",
      "}",
      "function main(x: Root) returns (word) {",
      "    return 0;",
      "}"]),
  ("growing_alias", "non-regular", "Nest", false,
    String.intercalate "\n" [
      "pragma solcore;",
      "",
      "//~ layout: non-regular",
      "enum Box<a> {",
      "    Box(a)",
      "}",
      "type Wrapped(a) = Box<a>;",
      "enum Nest<a> {",
      "    Nil,",
      "    Cons(a, Nest<Wrapped<a>>)",
      "}",
      "function main(x: Nest<word>) returns (word) {",
      "    return 0;",
      "}"]),
  ("growing_alternative_box", "non-regular", "Nest", false,
    String.intercalate "\n" [
      "pragma solcore;",
      "",
      "//~ layout: non-regular",
      "enum Box<a> {",
      "    Box(a)",
      "}",
      "enum Nest<a, b> {",
      "    Nil,",
      "    Left(Nest<Box<b>, word>),",
      "    Right(Nest<word, a>)",
      "}",
      "function main(x: Nest<word, bool>) returns (word) {",
      "    return 0;",
      "}"]),
  ("growing_alternative_comptime", "non-regular", "Nest", false,
    String.intercalate "\n" [
      "pragma solcore;",
      "",
      "//~ layout: non-regular",
      "enum Box<a> {",
      "    Box(a)",
      "}",
      "enum Nest<a, b> {",
      "    Nil,",
      "    Left(Nest<comptime<b>, word>),",
      "    Right(Nest<word, a>)",
      "}",
      "function main(x: Nest<word, bool>) returns (word) {",
      "    return 0;",
      "}"]),
  ("growing_box", "non-regular", "Nest", false,
    String.intercalate "\n" [
      "pragma solcore;",
      "",
      "//~ layout: non-regular",
      "enum Box<a> {",
      "    Box(a)",
      "}",
      "enum Nest<a> {",
      "    Nil,",
      "    Cons(a, Nest<Box<a>>)",
      "}",
      "function main(x: Nest<word>) returns (word) {",
      "    return 0;",
      "}"]),
  ("growing_comptime", "non-regular", "Nest", false,
    String.intercalate "\n" [
      "pragma solcore;",
      "",
      "//~ layout: non-regular",
      "enum Box<a> {",
      "    Box(a)",
      "}",
      "enum Nest<a> {",
      "    Nil,",
      "    Next(Nest<comptime<a>>)",
      "}",
      "function main(x: Nest<word>) returns (word) {",
      "    return 0;",
      "}"]),
  ("growing_comptime_alias", "non-regular", "Nest", false,
    String.intercalate "\n" [
      "pragma solcore;",
      "",
      "//~ layout: non-regular",
      "enum Box<a> {",
      "    Box(a)",
      "}",
      "type Qualified(a) = comptime<a>;",
      "enum Nest<a> {",
      "    Nil,",
      "    Next(Nest<Qualified<a>>)",
      "}",
      "function main(x: Nest<word>) returns (word) {",
      "    return 0;",
      "}"]),
  ("growing_nested_box", "non-regular", "Nest", false,
    String.intercalate "\n" [
      "pragma solcore;",
      "",
      "//~ layout: non-regular",
      "enum Box<a> {",
      "    Box(a)",
      "}",
      "enum Nest<a> {",
      "    Nil,",
      "    Cons(Box<Box<Nest<Box<a>>>>)",
      "}",
      "function main(x: Nest<word>) returns (word) {",
      "    return 0;",
      "}"]),
  ("growing_nested_comptime", "non-regular", "Nest", false,
    String.intercalate "\n" [
      "pragma solcore;",
      "",
      "//~ layout: non-regular",
      "enum Box<a> {",
      "    Box(a)",
      "}",
      "enum Nest<a> {",
      "    Nil,",
      "    Next(Nest<comptime<comptime<a>>>)",
      "}",
      "function main(x: Nest<word>) returns (word) {",
      "    return 0;",
      "}"]),
  ("growing_product", "non-regular", "Nest", false,
    String.intercalate "\n" [
      "pragma solcore;",
      "",
      "//~ layout: non-regular",
      "enum Box<a> {",
      "    Box(a)",
      "}",
      "enum Nest<a> {",
      "    Nil,",
      "    Cons(a, (Nest<(a, a)>, word))",
      "}",
      "function main(x: Nest<word>) returns (word) {",
      "    return 0;",
      "}"]),
  ("growing_wrapped_comptime", "non-regular", "Nest", false,
    String.intercalate "\n" [
      "pragma solcore;",
      "",
      "//~ layout: non-regular",
      "enum Box<a> {",
      "    Box(a)",
      "}",
      "enum Nest<a> {",
      "    Nil,",
      "    Next(Box<Nest<comptime<a>>>)",
      "}",
      "function main(x: Nest<word>) returns (word) {",
      "    return 0;",
      "}"]),
  ("nested_box_inline", "finite-nonempty", "", true,
    String.intercalate "\n" [
      "pragma solcore;",
      "",
      "//~ layout: finite-nonempty",
      "enum Box<a> {",
      "    Box(a)",
      "}",
      "enum Choice<a> {",
      "    Empty,",
      "    Choice(a)",
      "}",
      "enum Product<a> {",
      "    Product(word, a)",
      "}",
      "function unwrap(value: Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<word>>>>>>>>>>>>>>>>>>>>>>>>) returns (word) {",
      "    match (value) {",
      "        case Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(payload)))))))))))))))))))))))) {",
      "            return payload;",
      "        }",
      "        default {",
      "            return 0;",
      "        }",
      "    }",
      "}",
      "function main(input: word) returns (word) {",
      "",
      "    return unwrap(Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(input)))))))))))))))))))))))));",
      "}"]),
  ("nested_box_sequential", "finite-nonempty", "", true,
    String.intercalate "\n" [
      "pragma solcore;",
      "",
      "//~ layout: finite-nonempty",
      "enum Box<a> {",
      "    Box(a)",
      "}",
      "enum Choice<a> {",
      "    Empty,",
      "    Choice(a)",
      "}",
      "enum Product<a> {",
      "    Product(word, a)",
      "}",
      "function unwrap(value: Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<word>>>>>>>>>>>>>>>>>>>>>>>>) returns (word) {",
      "    match (value) {",
      "        case Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(Box(payload)))))))))))))))))))))))) {",
      "            return payload;",
      "        }",
      "        default {",
      "            return 0;",
      "        }",
      "    }",
      "}",
      "function main(input: word) returns (word) {",
      "    let value1: Box<word> = Box(input);",
      "    let value2: Box<Box<word>> = Box(value1);",
      "    let value3: Box<Box<Box<word>>> = Box(value2);",
      "    let value4: Box<Box<Box<Box<word>>>> = Box(value3);",
      "    let value5: Box<Box<Box<Box<Box<word>>>>> = Box(value4);",
      "    let value6: Box<Box<Box<Box<Box<Box<word>>>>>> = Box(value5);",
      "    let value7: Box<Box<Box<Box<Box<Box<Box<word>>>>>>> = Box(value6);",
      "    let value8: Box<Box<Box<Box<Box<Box<Box<Box<word>>>>>>>> = Box(value7);",
      "    let value9: Box<Box<Box<Box<Box<Box<Box<Box<Box<word>>>>>>>>> = Box(value8);",
      "    let value10: Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<word>>>>>>>>>> = Box(value9);",
      "    let value11: Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<word>>>>>>>>>>> = Box(value10);",
      "    let value12: Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<word>>>>>>>>>>>> = Box(value11);",
      "    let value13: Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<word>>>>>>>>>>>>> = Box(value12);",
      "    let value14: Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<word>>>>>>>>>>>>>> = Box(value13);",
      "    let value15: Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<word>>>>>>>>>>>>>>> = Box(value14);",
      "    let value16: Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<word>>>>>>>>>>>>>>>> = Box(value15);",
      "    let value17: Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<word>>>>>>>>>>>>>>>>> = Box(value16);",
      "    let value18: Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<word>>>>>>>>>>>>>>>>>> = Box(value17);",
      "    let value19: Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<word>>>>>>>>>>>>>>>>>>> = Box(value18);",
      "    let value20: Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<word>>>>>>>>>>>>>>>>>>>> = Box(value19);",
      "    let value21: Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<word>>>>>>>>>>>>>>>>>>>>> = Box(value20);",
      "    let value22: Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<word>>>>>>>>>>>>>>>>>>>>>> = Box(value21);",
      "    let value23: Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<word>>>>>>>>>>>>>>>>>>>>>>> = Box(value22);",
      "    let value24: Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<Box<word>>>>>>>>>>>>>>>>>>>>>>>> = Box(value23);",
      "",
      "    return unwrap(value24);",
      "}"]),
  ("nested_mixed_inline", "finite-nonempty", "", true,
    String.intercalate "\n" [
      "pragma solcore;",
      "",
      "//~ layout: finite-nonempty",
      "enum Box<a> {",
      "    Box(a)",
      "}",
      "enum Choice<a> {",
      "    Empty,",
      "    Choice(a)",
      "}",
      "enum Product<a> {",
      "    Product(word, a)",
      "}",
      "enum Record<a> {",
      "    Record(a)",
      "}",
      "function unwrap(value: Box<Record<Product<Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<word>>>>>>>>>>>>>>>>>>>>>>>>) returns (word) {",
      "    match (value) {",
      "        case Box(Record(Product(_, Choice(Box(Record(Product(_, Choice(Box(Record(Product(_, Choice(Box(Record(Product(_, Choice(Box(Record(Product(_, Choice(Box(Record(Product(_, Choice(payload)))))))))))))))))))))))) {",
      "            return payload;",
      "        }",
      "        default {",
      "            return 0;",
      "        }",
      "    }",
      "}",
      "function main(input: word) returns (word) {",
      "",
      "    return unwrap(Box(Record(Product(0, Choice(Box(Record(Product(0, Choice(Box(Record(Product(0, Choice(Box(Record(Product(0, Choice(Box(Record(Product(0, Choice(Box(Record(Product(0, Choice(input)))))))))))))))))))))))));",
      "}"]),
  ("nested_mixed_sequential", "finite-nonempty", "", true,
    String.intercalate "\n" [
      "pragma solcore;",
      "",
      "//~ layout: finite-nonempty",
      "enum Box<a> {",
      "    Box(a)",
      "}",
      "enum Choice<a> {",
      "    Empty,",
      "    Choice(a)",
      "}",
      "enum Product<a> {",
      "    Product(word, a)",
      "}",
      "enum Record<a> {",
      "    Record(a)",
      "}",
      "function unwrap(value: Box<Record<Product<Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<word>>>>>>>>>>>>>>>>>>>>>>>>) returns (word) {",
      "    match (value) {",
      "        case Box(Record(Product(_, Choice(Box(Record(Product(_, Choice(Box(Record(Product(_, Choice(Box(Record(Product(_, Choice(Box(Record(Product(_, Choice(Box(Record(Product(_, Choice(payload)))))))))))))))))))))))) {",
      "            return payload;",
      "        }",
      "        default {",
      "            return 0;",
      "        }",
      "    }",
      "}",
      "function main(input: word) returns (word) {",
      "    let value1: Choice<word> = Choice(input);",
      "    let value2: Product<Choice<word>> = Product(0, value1);",
      "    let value3: Record<Product<Choice<word>>> = Record(value2);",
      "    let value4: Box<Record<Product<Choice<word>>>> = Box(value3);",
      "    let value5: Choice<Box<Record<Product<Choice<word>>>>> = Choice(value4);",
      "    let value6: Product<Choice<Box<Record<Product<Choice<word>>>>>> = Product(0, value5);",
      "    let value7: Record<Product<Choice<Box<Record<Product<Choice<word>>>>>>> = Record(value6);",
      "    let value8: Box<Record<Product<Choice<Box<Record<Product<Choice<word>>>>>>>> = Box(value7);",
      "    let value9: Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<word>>>>>>>>> = Choice(value8);",
      "    let value10: Product<Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<word>>>>>>>>>> = Product(0, value9);",
      "    let value11: Record<Product<Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<word>>>>>>>>>>> = Record(value10);",
      "    let value12: Box<Record<Product<Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<word>>>>>>>>>>>> = Box(value11);",
      "    let value13: Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<word>>>>>>>>>>>>> = Choice(value12);",
      "    let value14: Product<Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<word>>>>>>>>>>>>>> = Product(0, value13);",
      "    let value15: Record<Product<Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<word>>>>>>>>>>>>>>> = Record(value14);",
      "    let value16: Box<Record<Product<Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<word>>>>>>>>>>>>>>>> = Box(value15);",
      "    let value17: Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<word>>>>>>>>>>>>>>>>> = Choice(value16);",
      "    let value18: Product<Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<word>>>>>>>>>>>>>>>>>> = Product(0, value17);",
      "    let value19: Record<Product<Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<word>>>>>>>>>>>>>>>>>>> = Record(value18);",
      "    let value20: Box<Record<Product<Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<word>>>>>>>>>>>>>>>>>>>> = Box(value19);",
      "    let value21: Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<word>>>>>>>>>>>>>>>>>>>>> = Choice(value20);",
      "    let value22: Product<Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<word>>>>>>>>>>>>>>>>>>>>>> = Product(0, value21);",
      "    let value23: Record<Product<Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<word>>>>>>>>>>>>>>>>>>>>>>> = Record(value22);",
      "    let value24: Box<Record<Product<Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<Box<Record<Product<Choice<word>>>>>>>>>>>>>>>>>>>>>>>> = Box(value23);",
      "",
      "    return unwrap(value24);",
      "}"]),
  ("recursive_construction", "unsupported-recursive", "", true,
    String.intercalate "\n" [
      "pragma solcore;",
      "",
      "//~ layout: unsupported-recursive",
      "enum Chain {",
      "    End(word),",
      "    Link(word, Chain)",
      "}",
      "function inspect(value: Chain) returns (word) {",
      "    match (value) {",
      "        case Chain.End(payload) {",
      "            return payload;",
      "        }",
      "        case Chain.Link(head, _) {",
      "            return head;",
      "        }",
      "    }",
      "}",
      "function main(input: word) returns (word) {",
      "    let result: word = inspect(Chain.Link(input, Chain.End(0)));",
      "    return result;",
      "}"]),
  ("recursive_field_match", "unsupported-recursive", "", true,
    String.intercalate "\n" [
      "pragma solcore;",
      "",
      "//~ layout: unsupported-recursive",
      "enum Chain {",
      "    End(word),",
      "    Link(word, Chain)",
      "}",
      "function inspect(value: Chain) returns (word) {",
      "    match (value) {",
      "        case Chain.End(payload) {",
      "            return payload;",
      "        }",
      "        case Chain.Link(head, tail) {",
      "            return head;",
      "        }",
      "    }",
      "}",
      "function main(input: word) returns (word) {",
      "    let result: word = inspect(Chain.End(input));",
      "    return result;",
      "}"])
]

/-- A program that declares a non-regular type and never uses it, beside a regular recursive one it
runs: upstream lowers no layout for the unused type, and Lean's catalog never registers it. -/
private def unusedNonRegularWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "pragma solcore;", "",
    "enum Box<a> {", "    Box(a)", "}",
    "enum Nest<a> {", "    Nil,", "    Cons(a, Nest<Box<a>>)", "}",
    "enum Chain {", "    End(word),", "    Link(word, Chain)", "}",
    "function first(value: Chain) returns (word) {", "    match (value) {",
    "        case Chain.End(payload) {", "            return payload;", "        }",
    "        case Chain.Link(head, _) {", "            return head;", "        }", "    }", "}",
    "function main(input: word) returns (word) {",
    "    return first(Chain.Link(input, Chain.End(0)));", "}"] }]
}

/-- Upstream's unit test of mutual representation cycles (`layout_finiteness.rs`) as a source: `A`
holds a `B` of its parameter, and `B` an `A` of `argument`. -/
private def mutualWorkspace (argument : String) : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "pragma solcore;", "",
    "enum Box<a> {", "    Box(a)", "}",
    "enum A<a> {", "    Stop,", "    A(B<a>)", "}",
    "enum B<b> {", s!"    B(A<{argument}>)", "}",
    "function main(x: A<word>) returns (word) {", "    return 0;", "}"] }]
}

private def layoutOutcome (label : String) (raw : Workspace.RawWorkspace) (refusedAt : Option String)
    (runs : Bool) : IO Unit := do
  let program ← get s!"{label} check" (checkProgram raw)
  match compile raw [← seed program "main"] with
  | .error (.compilation (.compilation (.compatible (.catalog (.catalog (.nonRegularType id)))))) =>
      let named := (program.signatures.dataTypes.find? fun data => decide (data.id = id)).map (·.name)
      require (refusedAt.isSome && named == refusedAt) s!"{label} refused as non-regular at {reprStr named}"
  | .error error => throw (IO.userError s!"{label} refused otherwise: {(reprStr error).take 400}")
  | .ok compiled =>
      require refusedAt.isNone s!"{label} compiled"
      if runs then
        let session ← boot (← compiled.open)
        let key ← match compiled.keys[0]? with
          | some key => pure key
          | none => throw (IO.userError s!"{label} root missing")
        let completed ← execute session key [word 5]
        require (completed.value == word 5) s!"{label} gave {reprStr completed.value}"

/-- Row 6's step 3: upstream's layout finiteness, checked at each nominal registration. Every
non-regular layout is refused at once, naming the type that upstream's `SC0420` names; the finite
and regular recursive ones compile, and those whose `main` takes a word give 5. -/
private def runLayoutFixtures : IO Unit := do
  for (name, expectation, root, runs, text) in layoutFixtures do
    let raw : Workspace.RawWorkspace :=
      { entry := "main.solc", externalLibraries := [], mainSources := [{ path := "main.solc", content := text }] }
    layoutOutcome name raw (if expectation == "non-regular" then some root else none) runs
  layoutOutcome "an unused non-regular declaration" unusedNonRegularWorkspace none true
  layoutOutcome "a regular mutual cycle" (mutualWorkspace "b") none false
  layoutOutcome "a mutual cycle through Box" (mutualWorkspace "Box<b>") (some "A") false
  layoutOutcome "a mutual cycle through comptime" (mutualWorkspace "comptime<b>") (some "A") false
  IO.println "SOURCE_CORE_LAYOUT_FIXTURES_PASS: upstream's 26 layout fixtures give upstream's outcomes, every non-regular one refused at once at the type SC0420 names and every finite or regular recursive one compiled, the word-taking ones giving 5; an unused non-regular declaration is accepted, and of upstream's mutual cycles the regular one compiles while those through Box and comptime are refused"

/-- Row 9: implementation methods whose predicates are not their trait method's, as upstream's
`SC0249` allows. `Add<Box>.add` omits the trait method's `Box: BitNot`; `Add<Pair<A>>.add`
requires only its implementation's own `A: BitNot` and uses it; `Sub<Box>.sub` reorders the trait
method's two predicates and uses one. Each method's dictionary is selected from the caller's
evidence and its implementation's premises. -/
private def implMethodPredicateWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "pragma solcore;",
    "trait Marker<T> {}",
    "trait BitNot<T> { function bnot(value: T) returns (T); }",
    "trait Add<T> { function add(left: T, right: T) returns (T) where T: BitNot; }",
    "trait Sub<T> { function sub(left: T, right: T) returns (T) where T: BitNot, T: Marker; }",
    "enum Box { Wrap(word) }",
    "enum Pair<A> { Two(A, A) }",
    "impl Marker<Box> {}",
    "impl BitNot<Box> {",
    "    function bnot(value: Box) returns (Box) { match (value) { case Box.Wrap(x) { return Box.Wrap(x + 100); } } }",
    "}",
    "impl<A> BitNot<Pair<A>> where A: BitNot {",
    "    function bnot(value: Pair<A>) returns (Pair<A>) { match (value) { case Pair.Two(x, y) { return Pair.Two(~x, ~y); } } }",
    "}",
    "impl Add<Box> {",
    "    function add(left: Box, right: Box) returns (Box) {",
    "        match (left) { case Box.Wrap(x) { match (right) { case Box.Wrap(y) { return Box.Wrap(x + y); } } } }",
    "    }",
    "}",
    "impl<A> Add<Pair<A>> where A: BitNot {",
    "    function add(left: Pair<A>, right: Pair<A>) returns (Pair<A>) where A: BitNot {",
    "        match (left) { case Pair.Two(x, unused) { match (right) { case Pair.Two(other, y) { return Pair.Two(~x, ~y); } } } }",
    "    }",
    "}",
    "impl Sub<Box> {",
    "    function sub(left: Box, right: Box) returns (Box) where Box: Marker, Box: BitNot { return ~left; }",
    "}",
    "function first(value: Box) returns (word) { match (value) { case Box.Wrap(x) { return x; } } }",
    "function omitted(a: word, b: word) returns (word) { return first(Box.Wrap(a) + Box.Wrap(b)); }",
    "function restated(a: word, b: word) returns (word) {",
    "    let sum: Pair<Box> = Pair.Two(Box.Wrap(a), Box.Wrap(0)) + Pair.Two(Box.Wrap(0), Box.Wrap(b));",
    "    match (sum) { case Pair.Two(x, y) { return first(x) * 1000 + first(y); } }",
    "}",
    "function reordered(a: word, b: word) returns (word) { return first(Box.Wrap(a) - Box.Wrap(b)); }"] }]
}

private def runImplMethodPredicates : IO Unit := do
  let program ← get "impl method predicate check" (checkProgram implMethodPredicateWorkspace)
  let names := ["omitted", "restated", "reordered"]
  let compiled ← get "impl method predicate compilation"
    (compile implMethodPredicateWorkspace (← names.mapM (seed program)))
  let mut session ← boot (← compiled.open)
  for (index, arguments, expected) in ([(0, [2, 3], 5), (1, [1, 2], 101102), (2, [7, 9], 107)] :
      List (Nat × List Nat × Nat)) do
    let key ← match compiled.keys[index]? with
      | some key => pure key
      | none => throw (IO.userError "impl method predicate root missing")
    let completed ← execute session key (arguments.map word)
    require (completed.value == word expected)
      s!"{names[index]!}{reprStr arguments} gave {reprStr completed.value}"
    session := completed.session
  IO.println "SOURCE_CORE_IMPL_METHOD_PREDICATES_PASS: implementation methods that omit, restate or reorder their trait method's predicates, as upstream's SC0249 allows, compile and run, each dictionary selected from the caller's evidence and its implementation's premises"

private def defaultForTypeParameterWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "pragma solcore;",
    "trait BitNot<T> { function bnot(value: T) returns (T); }",
    "default impl<T> BitNot<T> { function bnot(value: T) returns (T) { return value; } }",
    "enum Coin { Head, Tail }",
    "impl BitNot<Coin> { function bnot(value: Coin) returns (Coin) { match (value) { case Coin.Head { return Coin.Tail; } case Coin.Tail { return Coin.Head; } } } }",
    "enum Plain { Head, Tail }",
    "enum Box<A> { Wrap(A) }",
    "function coin(value: Coin) returns (Word) { match (value) { case Coin.Head { return 1; } case Coin.Tail { return 2; } } }",
    "function plain(value: Plain) returns (Word) { match (value) { case Plain.Head { return 1; } case Plain.Tail { return 2; } } }",
    "function flip<T>(x: T) returns (T) where T: BitNot { return ~x; }",
    "function second<T>(x: T) returns ((Word, T)) { return ~(3, x); }",
    "function boxed<T>(x: Box<T>) returns (Box<T>) { return ~x; }",
    "function viaCoin() returns (Word) { return coin(flip(Coin.Head)); }",
    "function viaPlain() returns (Word) { return plain(flip(Plain.Head)); }",
    "function viaSecond() returns (Word) { match (second(Coin.Head)) { case (w, c) { return w * 10 + coin(c); } } }",
    "function viaBoxed() returns (Word) { match (boxed(Box.Wrap(Coin.Head))) { case Box.Wrap(c) { return coin(c); } } }"] }]
}

private def givenBelowAnImplementationWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "pragma solcore;",
    -- Upstream needs it for `impl<T> Sub<T> where T: BitNot` (`SC0213`).
    "pragma no-patterson-condition;",
    "trait BitNot<T> { function bnot(value: T) returns (T); }",
    "trait Add<T> { function add(left: T, right: T) returns (T); }",
    "trait Sub<T> { function sub(left: T, right: T) returns (T); }",
    "default impl<T> BitNot<T> { function bnot(value: T) returns (T) { return value; } }",
    "enum Coin { Head, Tail }",
    "impl BitNot<Coin> { function bnot(value: Coin) returns (Coin) { match (value) { case Coin.Head { return Coin.Tail; } case Coin.Tail { return Coin.Head; } } } }",
    "enum Plain { Head, Tail }",
    "enum Box<A> { Wrap(A) }",
    "impl<A> Add<Box<A>> where A: BitNot { function add(left: Box<A>, right: Box<A>) returns (Box<A>) { match (left) { case Box.Wrap(x) { return Box.Wrap(~x); } } } }",
    "default impl<T> Sub<T> { function sub(left: T, right: T) returns (T) { return right; } }",
    "impl<T> Sub<T> where T: BitNot { function sub(left: T, right: T) returns (T) { return ~left; } }",
    "function coin(value: Coin) returns (Word) { match (value) { case Coin.Head { return 1; } case Coin.Tail { return 2; } } }",
    "function plain(value: Plain) returns (Word) { match (value) { case Plain.Head { return 1; } case Plain.Tail { return 2; } } }",
    "function twice<T>(x: Box<T>) returns (Box<T>) where T: BitNot { return x + x; }",
    "function differ<T>(x: T, y: T) returns (T) where T: BitNot { return x - y; }",
    "function boxedCoin() returns (Word) { match (twice(Box.Wrap(Coin.Head))) { case Box.Wrap(c) { return coin(c); } } }",
    "function boxedPlain() returns (Word) { match (twice(Box.Wrap(Plain.Head))) { case Box.Wrap(p) { return plain(p); } } }",
    "function differCoin() returns (Word) { return coin(differ(Coin.Head, Coin.Tail)); }"] }]
}

private def runGivenBelowAnImplementation : IO Unit := do
  let program ← get "given below an implementation check" (checkProgram givenBelowAnImplementationWorkspace)
  let names := ["boxedCoin", "boxedPlain", "differCoin"]
  let compiled ← get "given below an implementation compilation"
    (compile givenBelowAnImplementationWorkspace (← names.mapM (seed program)))
  let mut session ← boot (← compiled.open)
  for (index, expected) in ([(0, 2), (1, 1), (2, 2)] : List (Nat × Nat)) do
    let key ← match compiled.keys[index]? with
      | some key => pure key
      | none => throw (IO.userError "given below an implementation root missing")
    let completed ← execute session key []
    require (completed.value == word expected)
      s!"{names[index]!} gave {reprStr completed.value}"
    session := completed.session
  IO.println "SOURCE_CORE_GIVEN_BELOW_AN_IMPLEMENTATION_PASS: a condition of an implementation, and of an ordinary generic one beside a default, comes from the body's where predicate, as upstream's local givens do, so at a type with its own implementation the caller's runs, where compile refused before, and at a type that only the default covers the default runs"

private def superclassesOfGivensWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "pragma solcore;",
    -- Upstream needs it for the restated closed conditions (`SC0213`).
    "pragma no-patterson-condition;",
    "trait BitNot<T> { function bnot(value: T) returns (T); }",
    "trait Sub<T> where T: BitNot { function sub(left: T, right: T) returns (T); }",
    "trait Mul<T> { function mul(left: T, right: T) returns (T); }",
    "default impl<T> BitNot<T> { function bnot(value: T) returns (T) { return value; } }",
    "enum Coin { Head, Tail }",
    "impl BitNot<Coin> { function bnot(value: Coin) returns (Coin) { match (value) { case Coin.Head { return Coin.Tail; } case Coin.Tail { return Coin.Head; } } } }",
    "enum Plain { Head, Tail }",
    "enum Box<A> { Wrap(A) }",
    "impl Sub<Coin> where Coin: BitNot { function sub(left: Coin, right: Coin) returns (Coin) { return left; } }",
    "impl Sub<Plain> where Plain: BitNot { function sub(left: Plain, right: Plain) returns (Plain) { return left; } }",
    "impl<A> Mul<Box<A>> where A: Sub { function mul(left: Box<A>, right: Box<A>) returns (Box<A>) { match (left) { case Box.Wrap(x) { return Box.Wrap(~x); } } } }",
    "function coin(value: Coin) returns (Word) { match (value) { case Coin.Head { return 1; } case Coin.Tail { return 2; } } }",
    "function plain(value: Plain) returns (Word) { match (value) { case Plain.Head { return 1; } case Plain.Tail { return 2; } } }",
    "function viaSub<T>(x: T) returns (T) where T: Sub { return ~x; }",
    "function viaCoin() returns (Word) { return coin(viaSub(Coin.Head)); }",
    "function viaPlain() returns (Word) { return plain(viaSub(Plain.Head)); }",
    "function boxedCoin() returns (Word) { match (Box.Wrap(Coin.Head) * Box.Wrap(Coin.Tail)) { case Box.Wrap(c) { return coin(c); } } }",
    "function boxedPlain() returns (Word) { match (Box.Wrap(Plain.Head) * Box.Wrap(Plain.Tail)) { case Box.Wrap(p) { return plain(p); } } }"] }]
}

private def runSuperclassesOfGivens : IO Unit := do
  let program ← get "superclasses of givens check" (checkProgram superclassesOfGivensWorkspace)
  let names := ["viaCoin", "viaPlain", "boxedCoin", "boxedPlain"]
  let compiled ← get "superclasses of givens compilation"
    (compile superclassesOfGivensWorkspace (← names.mapM (seed program)))
  let mut session ← boot (← compiled.open)
  for (index, expected) in ([(0, 2), (1, 1), (2, 2), (3, 1)] : List (Nat × Nat)) do
    let key ← match compiled.keys[index]? with
      | some key => pure key
      | none => throw (IO.userError "superclasses of givens root missing")
    let completed ← execute session key []
    require (completed.value == word expected)
      s!"{names[index]!} gave {reprStr completed.value}"
    session := completed.session
  IO.println "SOURCE_CORE_SUPERCLASSES_OF_GIVENS_PASS: a superclass of a function's given, and of an implementation's condition, is a given its caller proves, as upstream projects it, so at a type with its own implementation that one runs, where check or compile refused before, and at a type only the default covers the default runs"

private def impliedSuperclassesWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "pragma solcore;",
    "trait BitNot<T> { function bnot(value: T) returns (T); }",
    "trait Sub<T> where T: BitNot { function sub(left: T, right: T) returns (T); }",
    "default impl<T> BitNot<T> { function bnot(value: T) returns (T) { return value; } }",
    "enum Coin { Head, Tail }",
    "impl BitNot<Coin> { function bnot(value: Coin) returns (Coin) { match (value) { case Coin.Head { return Coin.Tail; } case Coin.Tail { return Coin.Head; } } } }",
    "enum Plain { Head, Tail }",
    "impl Sub<Coin> { function sub(left: Coin, right: Coin) returns (Coin) { return ~left; } }",
    "impl Sub<Plain> { function sub(left: Plain, right: Plain) returns (Plain) { return ~left; } }",
    "function coin(value: Coin) returns (Word) { match (value) { case Coin.Head { return 1; } case Coin.Tail { return 2; } } }",
    "function plain(value: Plain) returns (Word) { match (value) { case Plain.Head { return 1; } case Plain.Tail { return 2; } } }",
    "function viaSub<T>(x: T) returns (T) where T: Sub { return ~x; }",
    "function viaCoin() returns (Word) { return coin(viaSub(Coin.Head)); }",
    "function viaPlain() returns (Word) { return plain(viaSub(Plain.Head)); }",
    "function subCoin() returns (Word) { return coin(Coin.Head - Coin.Tail); }",
    "function subPlain() returns (Word) { return plain(Plain.Head - Plain.Tail); }"] }]
}

private def runImpliedSuperclasses : IO Unit := do
  let program ← get "implied superclasses check" (checkProgram impliedSuperclassesWorkspace)
  let names := ["viaCoin", "viaPlain", "subCoin", "subPlain"]
  let compiled ← get "implied superclasses compilation"
    (compile impliedSuperclassesWorkspace (← names.mapM (seed program)))
  let mut session ← boot (← compiled.open)
  for (index, expected) in ([(0, 2), (1, 1), (2, 2), (3, 1)] : List (Nat × Nat)) do
    let key ← match compiled.keys[index]? with
      | some key => pure key
      | none => throw (IO.userError "implied superclasses root missing")
    let completed ← execute session key []
    require (completed.value == word expected)
      s!"{names[index]!} gave {reprStr completed.value}"
    session := completed.session
  IO.println "SOURCE_CORE_IMPLIED_SUPERCLASSES_PASS: an implementation that does not restate its trait's superclass is checked where it is declared, as upstream's SC0248, and its body and its callers use that superclass's implementation at the type, its own at a type that has one and the default at a type that only the default covers"

private def literalElementRefsWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "pragma solcore;",
    "function bump(r: memref<uint256>) { let v: uint256 = CanStore.load(r); CanStore.store(r, v + uint256(1)); return; }",
    "function viaLet() returns (uint256) { let m: uint256[] = new uint256[](3); let r = lidx(m, 1); bump(r); return m[uint256(1)]; }",
    "function viaCall() returns (uint256) { let m: uint256[] = new uint256[](3); bump(lidx(m, 1)); return m[uint256(1)]; }",
    "function viaStore() returns (uint256) { let m: uint256[] = new uint256[](3); CanStore.store(lidx(m, 1), uint256(7)); return m[uint256(1)]; }",
    "function viaLoad() returns (uint256) { let m: uint256[] = new uint256[](3); m[uint256(1)] = uint256(9); return CanStore.load(lidx(m, 1)); }",
    "function pastTheEnd() returns (uint256) { let m: uint256[] = new uint256[](3); bump(lidx(m, 3)); return m[uint256(0)]; }"] }]
}

private def runLiteralElementRefs : IO Unit := do
  let program ← get "literal element references check" (checkProgram literalElementRefsWorkspace)
  let names := ["viaLet", "viaCall", "viaStore", "viaLoad", "pastTheEnd"]
  let compiled ← get "literal element references compilation"
    (compile literalElementRefsWorkspace (← names.mapM (seed program)))
  let mut session ← boot (← compiled.open)
  let key (index : Nat) : IO Key := match compiled.keys[index]? with
    | some key => pure key
    | none => throw (IO.userError "literal element references root missing")
  for (index, expected) in ([(0, 1), (1, 1), (2, 7), (3, 9)] : List (Nat × Nat)) do
    let completed ← execute session (← key index) []
    require (completed.value == word expected)
      s!"{names[index]!} gave {reprStr completed.value}"
    session := completed.session
  let _ ← panics session (← key 4) [] SourceCorePanics.outOfBounds "pastTheEnd"
  IO.println "SOURCE_CORE_LITERAL_ELEMENT_REFS_PASS: a literal lidx index takes uint256 as a read's does, as upstream's literal in lidx's generic bound does, in a let, as an argument and under CanStore.store and CanStore.load, and one past the array's end panics with 0x32"

private def methodPredicateSuperclassesWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "pragma solcore;",
    "trait BitNot<T> { function bnot(value: T) returns (T); }",
    "trait Sub<T> where T: BitNot { function sub(left: T, right: T) returns (T); }",
    "trait Add<T> where T: BitNot { function add(left: T, right: T) returns (T); }",
    "trait Mod<T> where T: Add { function mod(left: T, right: T) returns (T); }",
    "trait Mul<T> { function mul(left: T, right: T) returns (T) where T: Sub; }",
    "trait Div<T> { function div(left: T, right: T) returns (T) where T: Mod; }",
    "default impl<T> BitNot<T> { function bnot(value: T) returns (T) { return value; } }",
    "enum Coin { Head, Tail }",
    "impl BitNot<Coin> { function bnot(value: Coin) returns (Coin) { match (value) { case Coin.Head { return Coin.Tail; } case Coin.Tail { return Coin.Head; } } } }",
    "enum Plain { Head, Tail }",
    "impl Sub<Coin> { function sub(left: Coin, right: Coin) returns (Coin) { return left; } }",
    "impl Sub<Plain> { function sub(left: Plain, right: Plain) returns (Plain) { return left; } }",
    "impl Add<Coin> { function add(left: Coin, right: Coin) returns (Coin) { return left; } }",
    "impl Mod<Coin> { function mod(left: Coin, right: Coin) returns (Coin) { return left; } }",
    "impl<A> Mul<A> { function mul(left: A, right: A) returns (A) where A: Sub { return ~left; } }",
    "impl<A> Div<A> { function div(left: A, right: A) returns (A) where A: Mod { return ~left; } }",
    "function coin(value: Coin) returns (Word) { match (value) { case Coin.Head { return 1; } case Coin.Tail { return 2; } } }",
    "function plain(value: Plain) returns (Word) { match (value) { case Plain.Head { return 1; } case Plain.Tail { return 2; } } }",
    "function viaTwoGivens<U>(x: U, y: U) returns (U) where U: Sub, U: Add { return x * y; }",
    "function coinMethod() returns (Word) { return coin(Coin.Head * Coin.Tail); }",
    "function plainMethod() returns (Word) { return plain(Plain.Head * Plain.Tail); }",
    "function twoGivens() returns (Word) { return coin(viaTwoGivens(Coin.Head, Coin.Tail)); }",
    "function twoLevels() returns (Word) { return coin(Coin.Head / Coin.Tail); }"] }]
}

private def runMethodPredicateSuperclasses : IO Unit := do
  let program ← get "method predicate superclasses check"
    (checkProgram methodPredicateSuperclassesWorkspace)
  let names := ["coinMethod", "plainMethod", "twoGivens", "twoLevels"]
  let compiled ← get "method predicate superclasses compilation"
    (compile methodPredicateSuperclassesWorkspace (← names.mapM (seed program)))
  let mut session ← boot (← compiled.open)
  for (index, expected) in ([(0, 2), (1, 1), (2, 2), (3, 2)] : List (Nat × Nat)) do
    let key ← match compiled.keys[index]? with
      | some key => pure key
      | none => throw (IO.userError "method predicate superclasses root missing")
    let completed ← execute session key []
    require (completed.value == word expected)
      s!"{names[index]!} gave {reprStr completed.value}"
    session := completed.session
  IO.println "SOURCE_CORE_METHOD_PREDICATE_SUPERCLASSES_PASS: a superclass of an implementation method's own predicate is a given its caller proves, as upstream projects it, so the body runs the impl at a type with its own, the default at a type only the default covers, through a caller whose two givens reach it and two levels up"

private def runDefaultForTypeParameter : IO Unit := do
  let program ← get "default for a type parameter check" (checkProgram defaultForTypeParameterWorkspace)
  let names := ["viaCoin", "viaPlain", "viaSecond", "viaBoxed"]
  let compiled ← get "default for a type parameter compilation"
    (compile defaultForTypeParameterWorkspace (← names.mapM (seed program)))
  let mut session ← boot (← compiled.open)
  for (index, expected) in ([(0, 2), (1, 1), (2, 31), (3, 1)] : List (Nat × Nat)) do
    let key ← match compiled.keys[index]? with
      | some key => pure key
      | none => throw (IO.userError "default for a type parameter root missing")
    let completed ← execute session key []
    require (completed.value == word expected)
      s!"{names[index]!} gave {reprStr completed.value}"
    session := completed.session
  IO.println "SOURCE_CORE_DEFAULT_FOR_TYPE_PARAMETER_PASS: a generic that takes a type parameter's goal from a where predicate, as upstream's SC0207 requires, compiles and runs with the caller's implementation or, at a type that only the default covers, the default chosen at the call, and a default still decides a goal whose subject is a product with a word first or a nominal type of the parameter"

set_option maxRecDepth 2048 in
def run : IO Unit := do
  let program ← get "public check" (checkProgram workspace)
  let seeds ← ["make", "use", "recurse", "local", "mappingEcho", "spin", "make", "uninitialized", "marked", "builtinUse", "namedUse", "mixedUse", "nestedUse", "closureNestedUse", "distinctClosureUse", "integratedHistoryUse", "makePair", "touchThenFail"].mapM (seed program)
  let options : Options := {specializationBudget := 256, compilationFuel := 1000}
  let compiled ← get "public single compilation" (compile workspace seeds options)
  require (compiled.rootCount == 18 && compiled.keys[0]? == compiled.keys[6]?) "public roots lost duplicate ordering"
  let key (index : Nat) : IO Key := match compiled.keys[index]? with
    | some key => pure key | none => throw (IO.userError "public root missing")
  let opened ← compiled.openWithReceipt
  let artifact := opened.val
  let fresh ← artifact.bootstrapWithReceipt
  let bootstrap := fresh.val
  let first : {pending : Bootstrap artifact // bootstrap.resume 1 = .outOfFuel pending} ←
    match suspended : bootstrap.resume 1 with
    | .outOfFuel pending => pure ⟨pending, suspended⟩
    | _ => throw (IO.userError "public bootstrap did not suspend")
  let second : {pending : Bootstrap artifact // first.val.resume 1 = .outOfFuel pending} ←
    match suspended : first.val.resume 1 with
    | .outOfFuel pending => pure ⟨pending, suspended⟩
    | _ => throw (IO.userError "public bootstrap did not suspend twice")
  let completed : {session : Session artifact // bootstrap.ReadyAt (1 + (1 + 300000)) session} ←
    match ready : second.val.resume 300000 with
    | .ready session => pure ⟨session, .suspend first.property (.suspend second.property (.single ready))⟩
    | _ => throw (IO.userError "public bootstrap resume failed")
  let initial := completed.val
  require (artifact.rootCount == 18 && initial.functionCount == 0) "public artifact initialization changed roots/handles"
  let builtinInput ← get "fresh builtin handle" (← initial.builtinWithReceipt .wordToInteger)
  have _preservedFresh : initial.SameRuntime builtinInput.val.session := builtinInput.property.same_runtime
  let builtinApplied ← execute builtinInput.val.session (← key 9) [builtinInput.val.value]
  require (builtinApplied.value == .integer 9) "single builtin input lost its source function"
  let namedInput ← get "fresh named handle" (← initial.namedWithReceipt (← key 2))
  have _preservedFreshNamed : initial.SameRuntime namedInput.val.session := namedInput.property.same_runtime
  require (namedInput.val.session.heapSize == initial.heapSize &&
    namedInput.val.session.functionCount == 1) "named issuance changed initialized storage or handle count"
  let namedApplied ← execute namedInput.val.session (← key 10) [namedInput.val.value]
  require (namedApplied.value == word 31) "single named input lost its recursive global capture"
  match namedInput.val.session.start (← key 9) [namedInput.val.value] with
  | .error {code := .handleTypeMismatch _ _, ..} => pure ()
  | _ => throw (IO.userError "public named input bypassed its source function type")
  let mixedBuiltin ← get "builtin after named issuance" (← namedInput.val.session.builtinWithReceipt .wordToInteger)
  have _preservedMixed : initial.SameRuntime mixedBuiltin.val.session :=
    namedInput.property.same_runtime.trans mixedBuiltin.property.same_runtime
  require (mixedBuiltin.val.session.heapSize == initial.heapSize &&
    mixedBuiltin.val.session.functionCount == 2) "sequential issuance changed storage or lost a handle"
  let namedAgain ← get "named handle reuse after builtin issuance" (← mixedBuiltin.val.session.namedWithReceipt (← key 2))
  have _preservedReused : initial.SameRuntime namedAgain.val.session :=
    _preservedMixed.trans namedAgain.property.same_runtime
  require (namedAgain.val.value == namedInput.val.value && namedAgain.val.session.functionCount == 2 &&
    namedAgain.val.session.heapSize == initial.heapSize) "reissued named handle was not reused"
  let mixedTable : Value := .mapping .word .word [(word 3, word 7), (word 3, word 99)]
  let mixedApplied ← execute namedAgain.val.session (← key 11)
    [namedInput.val.value, word 3, mixedTable, mixedBuiltin.val.value, namedInput.val.value]
  require (mixedApplied.value == .integer 72) "mixed inputs lost data order, metadata or a repeated earlier handle"
  match namedAgain.val.session.start (← key 11)
      [mixedBuiltin.val.value, word 3, mixedTable, namedInput.val.value, namedInput.val.value] with
  | .error {code := .handleTypeMismatch _ _, ..} => pure ()
  | _ => throw (IO.userError "mixed inputs accepted handles in incompatible argument positions")
  let nestedSignature ← match program.signatures.dataTypes.filter (·.name == "NestedFunctions") with
    | [signature] => pure signature
    | _ => throw (IO.userError "nested callable data signature missing")
  let nestedConstructor ← match nestedSignature.constructors.filter (·.name == "Hold") with
    | [constructor] => pure constructor
    | _ => throw (IO.userError "nested callable constructor missing")
  let nestedMetadata : SourceInference.DataConstructorInstantiation := {
    constructor := nestedConstructor.id, parameterSubstitution := [],
    payloadTypes := nestedConstructor.payloadTypes, resultType := .nominal nestedSignature.id [] }
  let nestedHolder : Value := .constructed nestedMetadata [namedInput.val.value, mixedBuiltin.val.value]
  let nestedValueType : TypeSystem.Ty := .product (.function .word .word) .word
  let nestedTable : Value := .mapping .word nestedValueType
    [(word 3, .product namedInput.val.value (word 7)),
      (word 3, .product namedInput.val.value (word 99))]
  let nestedBundle : Value := .product nestedHolder (.product nestedTable mixedBuiltin.val.value)
  let nestedApplied ← execute namedAgain.val.session (← key 12) [nestedBundle]
  require (nestedApplied.value == .integer 71)
    "nested inputs lost constructor payloads, repeated handles or first-match mapping order"
  let wrongNestedTable : Value := .mapping .word nestedValueType
    [(word 3, .product mixedBuiltin.val.value (word 7))]
  match namedAgain.val.session.start (← key 12)
      [.product nestedHolder (.product wrongNestedTable mixedBuiltin.val.value)] with
  | .error {code := .handleTypeMismatch _ _, ..} => pure ()
  | _ => throw (IO.userError "nested mapping payload accepted an incompatible function handle")
  let wrongNestedHolder : Value := .constructed nestedMetadata [mixedBuiltin.val.value, mixedBuiltin.val.value]
  match namedAgain.val.session.start (← key 12)
      [.product wrongNestedHolder (.product nestedTable mixedBuiltin.val.value)] with
  | .error {code := .handleTypeMismatch _ _, ..} => pure ()
  | _ => throw (IO.userError "nested constructor payload accepted an incompatible function handle")
  let made ← execute initial (← key 0) [word 10]
  let first ← execute made.session (← key 1) [made.value, word 2]
  let second ← execute first.session (← key 1) [made.value, word 3]
  require (first.value == word 12 && second.value == word 13) "public closure calls did not restart from the captured seed"
  require (initial.heapSize < made.session.heapSize && made.session.heapSize < second.session.heapSize) "public session replaced its native heap"
  let independent ← execute second.session (← key 0) [word 100]
  let closureMutated ← execute independent.session (← key 1) [made.value, word 5]
  require (closureMutated.value == word 15) "used-session closure did not restart from its captured seed"
  let closureNamed ← get "named after closure allocation and calls"
    (← closureMutated.session.namedWithReceipt (← key 2))
  let closureBuiltin ← get "builtin after closure calls and named issuance"
    (← closureNamed.val.session.builtinWithReceipt .wordToInteger)
  have _preservedClosureState : closureMutated.session.SameRuntime closureBuiltin.val.session :=
    closureNamed.property.same_runtime.trans closureBuiltin.property.same_runtime
  require (closureBuiltin.val.session.heapSize == closureMutated.session.heapSize)
    "later function issuance changed the used closure heap"
  let closureHolder : Value := .constructed nestedMetadata [made.value, closureBuiltin.val.value]
  let closurePairType : TypeSystem.Ty := .product (.function .word .word) (.function .word .word)
  let closureTable : Value := .mapping .word closurePairType
    [(word 3, .product made.value closureNamed.val.value),
      (word 3, .product independent.value closureNamed.val.value)]
  let closureBundle : Value := .product closureHolder (.product closureTable closureBuiltin.val.value)
  let closureNested ← execute closureBuiltin.val.session (← key 13) [closureBundle]
  require (closureNested.value == .integer 59)
    "nested closure inputs lost their captures, repeated aliases or first-match mapping order"
  let closureContinued ← execute closureNested.session (← key 1) [made.value, word 1]
  require (closureContinued.value == word 11) "nested closure execution changed the captured seed"
  let independentContinued ← execute closureContinued.session (← key 1) [independent.value, word 1]
  require (independentContinued.value == word 101)
    "nested closure input aliased an independently allocated capture"
  let afterDistinctIssuance ← get "new named handle after both closure calls"
    (← independentContinued.session.namedWithReceipt (← key 0))
  have _preservedDistinctState : independentContinued.session.SameRuntime afterDistinctIssuance.val.session :=
    afterDistinctIssuance.property.same_runtime
  require (afterDistinctIssuance.val.session.heapSize == independentContinued.session.heapSize &&
    afterDistinctIssuance.val.session.functionCount == independentContinued.session.functionCount + 1)
    "new factory issuance changed capture storage or failed to extend the handle registry"
  let distinctTable : Value := .mapping .word closurePairType
    [(word 3, .product made.value independent.value),
      (word 3, .product independent.value made.value)]
  let distinctBundle : Value := .product made.value distinctTable
  let distinctApplied ← execute afterDistinctIssuance.val.session (← key 14) [distinctBundle]
  require (distinctApplied.value == word 135)
    "two nested closure inputs lost their captures, repeated aliases or ordered entries"
  let firstDistinct ← execute distinctApplied.session (← key 1) [made.value, word 1]
  require (firstDistinct.value == word 11) "first closure changed its captured seed after distinct input execution"
  let secondDistinct ← execute firstDistinct.session (← key 1) [independent.value, word 1]
  require (secondDistinct.value == word 101) "second closure changed its captured seed after distinct input execution"
  let captured ← get "snapshot of both called closures" (← secondDistinct.session.snapshotWithReceipt)
  have _captured : secondDistinct.session.SnapshotAt 1024 captured.val := captured.property
  let afterCapture ← execute secondDistinct.session (← key 1) [made.value, word 9]
  require (afterCapture.value == word 19) "original closure did not restart from its seed after snapshot capture"
  let restored ← match afterCapture.session.restoreSnapshot captured.val with
    | .ok (.ready session) => pure session
    | _ => throw (IO.userError "captured ready session did not restore through its original ownership domain")
  require (restored.heapSize == secondDistinct.session.heapSize && restored.heapSize < afterCapture.session.heapSize)
    "restoration retained later allocations or replayed initialization"
  let restoredFirst ← execute restored (← key 1) [made.value, word 1]
  require (restoredFirst.value == word 11)
    "restoration used post-snapshot storage or lost the original closure handle"
  let restoredSecond ← execute restoredFirst.session (← key 1) [independent.value, word 1]
  require (restoredSecond.value == word 101)
    "restoration lost the second original handle or aliased its independent capture"
  let integratedNamed ← get "named receipt after distinct closure calls"
    (← secondDistinct.session.namedWithReceipt (← key 2))
  let integratedBuiltin ← get "builtin receipt after distinct closure calls"
    (← integratedNamed.val.session.builtinWithReceipt .wordToInteger)
  have _preservedIntegratedState : secondDistinct.session.SameRuntime integratedBuiltin.val.session :=
    integratedNamed.property.same_runtime.trans integratedBuiltin.property.same_runtime
  require (integratedNamed.val.value == closureNamed.val.value &&
    integratedBuiltin.val.value == closureBuiltin.val.value &&
    integratedBuiltin.val.session.functionCount == secondDistinct.session.functionCount &&
    integratedBuiltin.val.session.heapSize == secondDistinct.session.heapSize)
    "used-session issuance changed captures or failed to reuse existing function handles"
  let integratedHolder : Value := .constructed nestedMetadata [made.value, integratedBuiltin.val.value]
  let integratedBundle : Value := .product integratedHolder (.product distinctTable integratedNamed.val.value)
  let integratedApplied ← execute integratedBuiltin.val.session (← key 15) [integratedBundle]
  require (integratedApplied.value == .integer 166)
    "combined retained and issued function inputs lost captures, aliases, recursive code or mapping order"
  let firstIntegrated ← execute integratedApplied.session (← key 1) [made.value, word 1]
  require (firstIntegrated.value == word 11) "combined execution changed the older closure's captured seed"
  let secondIntegrated ← execute firstIntegrated.session (← key 1) [independent.value, word 1]
  require (secondIntegrated.value == word 101) "combined execution changed the independent closure's captured seed"
  let wrongIntegratedTable : Value := .mapping .word closurePairType
    [(word 3, .product made.value integratedBuiltin.val.value)]
  match integratedBuiltin.val.session.start (← key 15)
      [.product integratedHolder (.product wrongIntegratedTable integratedNamed.val.value)] with
  | .error {code := .handleTypeMismatch _ _, ..} => pure ()
  | _ => throw (IO.userError "combined nested input accepted a builtin in a retained closure position")
  let paired ← execute initial (← key 16) [word 10, word 100]
  let (pairLeft, pairRight) ← match paired.value with
    | .product left@(.function _) right@(.function _) => pure (left, right)
    | _ => throw (IO.userError "product output did not export both captured functions")
  require (pairLeft != pairRight) "independently captured product outputs shared one public handle"
  let pairFirst ← execute paired.session (← key 1) [pairLeft, word 2]
  let pairSecond ← execute pairFirst.session (← key 1) [pairRight, word 3]
  require (pairFirst.value == word 12 && pairSecond.value == word 103)
    "product output lost an independent capture or the earlier sibling handle"
  let pairData ← execute pairSecond.session (← key 2) [word 2]
  require (pairData.value == word 31) "intervening data execution changed recursive behavior"
  let pairTable : Value := .mapping .word closurePairType
    [(word 3, .product pairLeft pairRight), (word 3, .product pairRight pairLeft)]
  let pairNested ← execute pairData.session (← key 14) [.product pairLeft pairTable]
  require (pairNested.value == word 135)
    "product-exported functions lost their captures or a repeated nested alias"
  let pairLeftContinued ← execute pairNested.session (← key 1) [pairLeft, word 1]
  let pairRightContinued ← execute pairLeftContinued.session (← key 1) [pairRight, word 1]
  require (pairLeftContinued.value == word 11 && pairRightContinued.value == word 101)
    "reused product outputs changed their captured seeds or first-match mapping order"
  let touching ← pairRightContinued.session.runWithReceipt (← key 17) [pairLeft, word 9]
    {executionFuel := 300000}
  let failedPair ← match touching.val with
    | .ok (.failed reason session) =>
        match ← get "closure call before failure diagnostic" (session.diagnostic (← key 17) reason) with
        | some {error := .uninitializedLocal _, span := some _, ..} => pure session
        | _ => throw (IO.userError "failure after a closure call lost its actual source diagnosis")
    | _ => throw (IO.userError "closure call followed by failure changed outcome")
  let afterFailedData ← execute failedPair (← key 2) [word 2]
  require (afterFailedData.value == word 31) "data execution could not continue after a closure call and failure"
  let afterFailedLeft ← execute afterFailedData.session (← key 1) [pairLeft, word 1]
  let afterFailedRight ← execute afterFailedLeft.session (← key 1) [pairRight, word 1]
  require (afterFailedLeft.value == word 11 && afterFailedRight.value == word 101)
    "failure lost a retained handle or changed a captured seed"
  let recursive ← execute second.session (← key 2) [word 5]
  require (recursive.value == word 31) "public recursive result changed"
  let localResult ← execute recursive.session (← key 3) [.bool true]
  require (localResult.value == .product (word 7) (.bool true)) "public local specialization changed"
  let raw : Value := .mapping (.comptime .word) (.comptime .word) [(word 1, word 7), (word 1, word 9)]
  let mapped ← execute localResult.session (← key 4) [raw]
  require (mapped.value == raw) "public value lost raw mapping metadata or duplicate order"
  let started ← get "public call start" (mapped.session.start (← key 1) [made.value, word 4])
  let suspended ← started.resumeWithReceipt 1
  let checkpoint ← match suspended.val with
    | .outOfFuel checkpoint => pure checkpoint | _ => throw (IO.userError "public call did not suspend")
  let finished ← checkpoint.resumeWithReceipt 300000
  let resumed ← match finished.val with
    | .succeeded result => pure result | _ => throw (IO.userError "public call did not resume")
  require (resumed.value == word 14) "public checkpoint lost capture"
  let namedReceipt ← get "public named handle" (← resumed.session.namedWithReceipt (← key 2))
  let named := namedReceipt.val
  have _preservedNamed : resumed.session.SameRuntime named.session := namedReceipt.property.same_runtime
  let namedResult ← execute named.session (← key 1) [named.value, word 4]
  require (namedResult.value == word 31) "public named handle lost cached code"
  let builtinReceipt ← get "public builtin handle" (← namedResult.session.builtinWithReceipt .wordToInteger)
  let builtin := builtinReceipt.val
  have _preservedBuiltin : namedResult.session.SameRuntime builtin.session := builtinReceipt.property.same_runtime
  discard <| get "public builtin authentication"
    (builtin.session.authenticate 1024 (.function .word .integer) builtin.value)
  let afterFault ← match ← builtin.session.run (← key 7) [] {executionFuel := 300000} with
    | .ok (.failed reason session) =>
        match ← get "public language diagnostic" (session.diagnostic (← key 7) reason) with
        | some {error := .uninitializedLocal _, span := some _, ..} => pure session
        | _ => throw (IO.userError "public failure lost classification/site/span")
    | _ => throw (IO.userError "public uninitialized read changed outcome")
  let other ← compiled.open
  let foreign ← boot other
  match ← foreign.run (← key 1) [made.value, word 1] {executionFuel := 300000} with
  | .error {code := .foreignArtifact, ..} => pure ()
  | _ => throw (IO.userError "public boundary accepted foreign handle")
  let directStart ← get "public direct handle start"
    (afterFault.startHandlePacked (← handle made.value) (word 4))
  let directPending ← match ← directStart.resume 0 with
    | .outOfFuel pending => pure pending
    | _ => throw (IO.userError "public direct call did not suspend at zero fuel")
  let direct ← match ← directPending.resume 300000 with
    | .succeeded completion => pure completion
    | _ => throw (IO.userError "public direct call did not resume")
  require (direct.value == word 14) "public direct invocation lost its capture"
  let integer ← match ← direct.session.invokePacked (← handle builtin.value) (word 8) {executionFuel := 300000} with
    | .ok (.succeeded completion) => pure completion
    | _ => throw (IO.userError "public direct builtin invocation failed")
  require (integer.value == .integer 8) "public direct builtin changed result"
  let absent ← get "public direct failing handle" (← integer.session.named (← key 7))
  let absentHandle ← handle absent.value
  let afterDirectFault ← match ← absent.session.invokePacked absentHandle .unit {executionFuel := 300000} with
    | .ok (.failed reason session) =>
        match ← get "public direct diagnostic" (session.handleDiagnostic absentHandle reason) with
        | some {error := .uninitializedLocal _, span := some _, ..} => pure session
        | _ => throw (IO.userError "public direct fault lost source diagnosis")
    | _ => throw (IO.userError "public direct fault changed outcome")
  let marked ← get "public marked handle" (← afterDirectFault.named (← key 8))
  match marked.session.startHandlePacked (← handle marked.value) (.bool true) 0 with
  | .error {code := .stagedInvocationRequired _, ..} => pure ()
  | _ => throw (IO.userError "public direct invocation bypassed source staging guard")
  match foreign.startHandlePacked (← handle made.value) (word 1) with
  | .error {code := .foreignArtifact, ..} => pure ()
  | _ => throw (IO.userError "public direct invocation accepted a foreign artifact handle")
  let spinning ← get "public spin start" (afterFault.start (← key 5) [])
  let spinning ← match ← spinning.resume 200 with
    | .outOfFuel next => pure next | _ => throw (IO.userError "public spin completed")
  match ← spinning.resume 300 with
  | .outOfFuel _ => pure () | _ => throw (IO.userError "public resumed spin completed")
  let empty ← get "public empty compilation" (compileChecked program [] options)
  let emptyArtifact ← empty.open
  let emptySession ← boot emptyArtifact
  require (emptyArtifact.rootCount == 0 && emptySession.heapSize == 0) "empty public artifact invented callable state"
  match ← emptySession.run (← key 0) [] with
  | .error {code := .missingEntry _, ..} => pure ()
  | _ => throw (IO.userError "empty public session accepted a call")
  match emptySession.startHandlePacked (← handle made.value) (word 1) with
  | .error {code := .unknownHandle, ..} => pure ()
  | _ => throw (IO.userError "empty public session accepted a callable handle")
  let mainCompiled ← get "public conventional main" (compileEntry workspace options)
  require (mainCompiled.rootCount == 1) "public main gained another root"
  let mainArtifact ← mainCompiled.open
  let mainSession ← boot mainArtifact
  let mainKey ← match mainCompiled.keys.head? with
    | some key => pure key | none => throw (IO.userError "public main missing")
  let mainResult ← execute mainSession mainKey []
  require (mainResult.value == word 55) "public conventional main changed result"
  let abi ← get "public Static Word compilation" (compileStaticWord workspace options)
  let abiRoot ← match abi.roots with
    | [root] => pure root | _ => throw (IO.userError "public ABI changed exported root set")
  require (abi.count == 1 && abiRoot.metadata.name.text == "recurse" &&
    (abi.rootForSelector? abiRoot.metadata.selector).isSome) "public ABI lost selector metadata"
  let abiArtifact ← abi.compiled.open
  let abiSession ← boot abiArtifact
  let abiResult ← execute abiSession abiRoot.root.key [word 3]
  require (abiResult.value == word 31) "public ABI root changed execution"
  runCaptures
  runClosureParameterFixtures
  runLayoutBound
  runLayoutFixtures
  runImplMethodPredicates
  runDefaultForTypeParameter
  runGivenBelowAnImplementation
  runSuperclassesOfGivens
  runImpliedSuperclasses
  runLiteralElementRefs
  runMethodPredicateSuperclasses

end Tests.SourceCoreExecution
end
