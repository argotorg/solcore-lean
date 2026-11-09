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
  mainSources := [{ path := "main.solc", content := source }]
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
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
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

def run : IO Unit := do
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
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
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
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "type F = function(Word) returns (Word);",
    "function maker(value: Word) returns (F) { return lam(delta: Word) -> Word { value = value + delta; return value; }; }",
    "function zero() returns (function() returns (Word)) { return lam() -> Word { return 7; }; }",
    "function unused(value: Word) returns (Word) { let ignored = lam(item) { return item; }; return value; }",
    "function poly(flag: Bool) returns (Word, Bool) { let f = lam(item) { return item; }; return (f(1), f(flag)); }",
    "function loop(value: Word) returns (F) { let f: F; while (true) { f = lam(delta: Word) -> Word { value = value + delta; return value; }; break; } return f; }",
    "function nestedPoly(flag: Bool) returns (Word, Word) { let outer = lam(value) { let inner = lam(item) { return item; }; return inner(1); }; return (outer(1), outer(flag)); }"
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
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
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
  mainSources := [{path := "main.solc", content :=
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
  entry := "api.solc", externalLibraries := [], mainSources := [{path := "api.solc", content}] }
private def workspace : Workspace.RawWorkspace := {
  entry := "api.solc", externalLibraries := [], mainSources := [
    {path := "api.solc", content := String.intercalate "\n" [
      "import {twice as doubled, recursive} from provider;",
      "function main() returns (Word) { return 17; }",
      "function local(value: Word) returns (Word) { return value + 1; }",
      "function hidden(value: Word) returns (Word) { return value; }",
      "export {doubled, local, recursive};"]},
    {path := "provider.solc", content := String.intercalate "\n" [
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
  mainSources := [{path := "main.solc", content := String.intercalate "\n" lines}] }

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
  entry := "main.solc", mainSources := [{ path := "main.solc", content }], externalLibraries := [] }

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
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
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
    "function nested(flag: Bool) returns (Word, Word) { let outer = lam(item) { keep(item); let inner = lam(value) { return keep(value); }; return inner(1); }; return (outer(13), outer(flag)); }",
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
  let program ← match checkProgram {entry := "main.solc", mainSources := [{path := "main.solc", content}], externalLibraries := []} with
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
  let program ← match checkProgram {entry := "main.solc", mainSources := [{path := "main.solc", content}], externalLibraries := []} with
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
      entry := "main.solc", mainSources := [{ path := "main.solc", content }], externalLibraries := [] } with
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
  mainSources := [{ path := "main.solc", content }]
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
  mainSources := [{path := "main.solc", content := String.intercalate "\n" lines}] }

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
  mainSources := [{path := "main.solc", content := String.intercalate "\n" lines}] }

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
  rejectedByInference "no operator on uint8 yet" ["function bad(x: uint8) returns (uint8) { return x + x; }"]
  rejectedByInference "no literal at uint8 yet" ["function bad() returns (uint8) { return 5; }"]
  IO.println "SOURCE_CORE_FIXED_TYPES_PASS: the twelve fixed-width integer types as parameters, results, locals and mapping elements hold canonical words, a missing element is zero, non-canonical arguments are rejected before the body runs, the types are distinct from each other and from Word, and operators and literals at them are not yet accepted"

end Tests.SourceCoreFixedIntegerTypes
end

section
/-! The first operators on the twelve fixed-width integer types, through the
public source API: `==` and `!=` on every type, and `< > <= >=` and `& | ^` on
the unsigned types. On canonical words they are Word's operators, and the
bitwise results stay canonical. Signed orderings and bitwise operators, `~` and
the checked arithmetic come with the next steps and are still rejected. -/
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
  mainSources := [{path := "main.solc", content := String.intercalate "\n" lines}] }
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
  "function mixed(x: uint8, y: uint8) returns (uint8) { let both: uint8 = x & y; return both | (x ^ y); }"
]

private def names : List String :=
  ["eq8", "ne16", "lt32", "le64", "gt128", "ge256", "and8", "or16", "xor32", "eqSigned", "mixed"]

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
    (10, [word 0xF0, word 0x3C], word 0xFC)]
  for (index, arguments, expected) in cases do
    let completed ← execute session (← key index) arguments
    require (completed.value == expected)
      s!"{names[index]?} on {reprStr arguments} gave {reprStr completed.value}"
    session := completed.session
  rejectedByInference "signed ordering is not yet a builtin"
    ["function bad(x: int8, y: int8) returns (bool) { return x < y; }"]
  rejectedByInference "signed bitwise is not yet a builtin"
    ["function bad(x: int8, y: int8) returns (int8) { return x & y; }"]
  rejectedByInference "checked arithmetic is not yet a builtin"
    ["function bad(x: uint8, y: uint8) returns (uint8) { return x + y; }"]
  rejectedByInference "operands of different types"
    ["function bad(x: uint8, y: uint16) returns (bool) { return x == y; }"]
  rejectedByInference "compound assignment is not yet defined"
    ["function bad(x: uint8, y: uint8) returns (uint8) { x &= y; return x; }"]
  IO.println "SOURCE_CORE_FIXED_OPERATORS_PASS: == and != on signed and unsigned fixed-width types, < > <= >= and & | ^ on unsigned ones, with canonical results, and signed orderings, signed bitwise operators, checked arithmetic, compound assignment and mixed operand types still rejected"

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
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
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
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
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

end Tests.SourceCoreExecution
end
