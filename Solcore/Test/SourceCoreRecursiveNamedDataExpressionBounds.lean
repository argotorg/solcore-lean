import Solcore.SourceSemantics.CoreLowering.RecursiveNamedDataExpressionHeadBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionCompositionsBounds
import Solcore.Test.SourceCoreRecursiveNamedExpressionBounds

/-! Concrete named/builtin leaves discharge the inclusive data-head contracts.
Actual constructor/index compilation checks raw metadata, ordered effects and
faults. Positional members use retained typed IR and the actual branch generator;
the surface parser's syntax is not enlarged. Whole Tree/callee closure is later. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedDataExpressionBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableAncestryPairedLookup
open CallableIndexedHistory SourceCoreCallableIndexedFrames RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds
open CompatibleExpressionTypedCompositions

#check_failure RecursiveNamedDataExpressionHeadBounds.Tree
#check_failure RecursiveNamedDataExpressionHeadBounds.BodyMeaning
#check_failure SourceTypedRuntime.run

section ConcreteBodies
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations}
  {capturePrefix : Nat} {registry : SourceCoreRawMetadata.Registry}
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (body : BuiltinNamedCalls.Body prepared values ambient.definitions program)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (body.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

variable {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {readFuel : Nat}
  {compilation : SourceCoreFunctions.Context}
  (callerValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))


private def Leaf : GenericExpressionMeaning.Certificate := fun scope id lowered =>
  RecursiveNamedCatalog.Head [Header.of_body body] compilation source context
    (CompatibleExpressionBuiltins.Tree readFuel values source context solved reasonAt) scope id lowered ∨
  CompatibleExpressionBuiltins.Tree readFuel values source context solved reasonAt scope id lowered

include extension uninitialized missing faithful functionLeaves functionTypes callerValid unique owners callerUninitialized callerMissing in
theorem leaf_preserves_at (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Leaf body (source := source) (context := context) (compilation := compilation) (solved := solved) (reasonAt := reasonAt) (readFuel := readFuel)) faults
      (protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix) := by
  intro scope id lowered certificate
  change _ ∨ _ at certificate
  cases certificate with
  | inl named =>
    exact SourceCoreRecursiveNamedExpressionBounds.builtin_named_preserves_at functions extension body uninitialized missing faithful functionLeaves functionTypes
      callerValid unique owners callerUninitialized callerMissing budget size within named
  | inr builtin =>
    exact RecursiveNamedBoundedContracts.preserves_at_of_unbounded
      (ProtectedExpressionMeaning.preserves_of_typed _
        (CompatibleExpressionBuiltins.preserves functions extension faithful functionLeaves functionTypes
          program evidence callerValid unique callerUninitialized callerMissing)) size builtin

include extension uninitialized missing faithful functionLeaves functionTypes callerValid callerUninitialized callerMissing in
theorem leaf_reflects_at (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Leaf body (source := source) (context := context) (compilation := compilation) (solved := solved) (reasonAt := reasonAt) (readFuel := readFuel)) faults
      (protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix) := by
  intro scope id lowered certificate
  change _ ∨ _ at certificate
  cases certificate with
  | inl named =>
    exact SourceCoreRecursiveNamedExpressionBounds.builtin_named_reflects_at functions extension body uninitialized missing faithful functionLeaves functionTypes
      callerValid callerUninitialized callerMissing budget size within named
  | inr builtin =>
    exact RecursiveNamedBoundedContracts.reflects_at_of_unbounded
      (ProtectedExpressionMeaning.reflects_of_typed _
        (CompatibleExpressionBuiltins.reflects functions extension faithful functionLeaves functionTypes
          program evidence callerValid callerUninitialized callerMissing)) size builtin


private def Calls : CompatibleExpressionCalls.CallHeads :=
  RecursiveNamedCatalog.Head [Header.of_body body] compilation source context

include extension uninitialized missing faithful functionLeaves functionTypes callerValid unique owners callerUninitialized callerMissing in
theorem data_preserves_at (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (RecursiveNamedDataExpressionHeadBounds.Certificate
        (Calls body (source := source) (context := context) (compilation := compilation)) values source context reasonAt
        (Leaf body (source := source) (context := context) (compilation := compilation) (solved := solved) (reasonAt := reasonAt) (readFuel := readFuel))) faults
      (protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix) := by
  apply RecursiveNamedDataExpressionHeadBounds.preserves_at functions extension faithful functionLeaves functionTypes
    program evidence unique callerMissing entry_transport budget size within
  intro child childWithin
  exact leaf_preserves_at functions extension body uninitialized missing faithful functionLeaves functionTypes
    callerValid unique owners callerUninitialized callerMissing budget child childWithin

include extension uninitialized missing faithful functionLeaves functionTypes callerValid callerUninitialized callerMissing in
theorem data_reflects_at (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (RecursiveNamedDataExpressionHeadBounds.Certificate
        (Calls body (source := source) (context := context) (compilation := compilation)) values source context reasonAt
        (Leaf body (source := source) (context := context) (compilation := compilation) (solved := solved) (reasonAt := reasonAt) (readFuel := readFuel))) faults
      (protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix) := by
  apply RecursiveNamedDataExpressionHeadBounds.reflects_at functions extension faithful functionLeaves functionTypes
    program evidence callerMissing entry_transport budget size within
  intro child childWithin
  exact leaf_reflects_at functions extension body uninitialized missing faithful functionLeaves functionTypes
    callerValid callerUninitialized callerMissing budget child childWithin

include extension uninitialized missing faithful functionLeaves functionTypes callerValid unique owners callerUninitialized callerMissing in
/-- A primitive parent consumes the same data-head budget. -/
theorem parent_preserves_at (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (Head values.checked source
        (RecursiveNamedDataExpressionHeadBounds.Certificate
          (Calls body (source := source) (context := context) (compilation := compilation)) values source context reasonAt
          (Leaf body (source := source) (context := context) (compilation := compilation) (solved := solved) (reasonAt := reasonAt) (readFuel := readFuel)))) faults
      (protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix) := by
  apply RecursiveNamedExpressionCompositionsBounds.Head.preserves_at functions program evidence entry_transport budget size within unique
  intro child childWithin
  exact data_preserves_at functions extension body uninitialized missing faithful functionLeaves functionTypes
    callerValid unique owners callerUninitialized callerMissing budget child childWithin

include extension uninitialized missing faithful functionLeaves functionTypes callerValid callerUninitialized callerMissing in
theorem parent_reflects_at (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (Head values.checked source
        (RecursiveNamedDataExpressionHeadBounds.Certificate
          (Calls body (source := source) (context := context) (compilation := compilation)) values source context reasonAt
          (Leaf body (source := source) (context := context) (compilation := compilation) (solved := solved) (reasonAt := reasonAt) (readFuel := readFuel)))) faults
      (protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix) := by
  apply RecursiveNamedExpressionCompositionsBounds.Head.reflects_at functions program evidence entry_transport budget size within
  intro child childWithin
  exact data_reflects_at functions extension body uninitialized missing faithful functionLeaves functionTypes
    callerValid callerUninitialized callerMissing budget child childWithin
end ConcreteBodies

private def content : String := String.intercalate "\n" [
  "enum Box { Box(Bool) }", "enum Row { Row(Word, Bool) }",
  "enum Key { Key(Bool) }", "enum Missing { Missing(Word) }",
  "function side(n: Word) returns (Word) { let saved = n; return saved; }",
  "function truth(flag: Bool) returns (Bool) { let saved = flag; return saved; }",
  "function failWord() returns (Word) { let written = 5; let gap: Word; return gap; }",
  "function badBool() returns (Bool) { let written = 19; let gap: Bool; return gap; }",
  "function filled() returns (mapping(Bool => Bool)) { let m: mapping(Bool => Bool); m[true] = true; return m; }",
  "function empty() returns (mapping(Bool => Bool)) { let m: mapping(Bool => Bool); return m; }",
  "function badMap() returns (mapping(Bool => Bool)) { let written = 23; let gap: Word; gap; let m: mapping(Bool => Bool); return m; }",
  "function single() returns (Box) { return Box(truth(true)); }",
  "function row() returns (Row) { return Row(side(7), truth(false)); }",
  "function nominalKey() returns (Bool) { let m: mapping(Key => Bool); return m[Key(truth(true))]; }",
  "function productKey() returns (Bool) { let m: mapping((Bool, Bool) => Bool); return m[(truth(true), truth(false))]; }",
  "function duplicate(m: mapping((Bool, Bool) => Bool)) returns (Bool) { return m[(truth(true), truth(false))]; }",
  "function baseIndex() returns (Bool) { return filled()[truth(true)]; }",
  "function lazyIndex() returns (Bool) { return empty()[truth(true)]; }",
  "function operatorParent() returns (Bool) { return !filled()[truth(true)]; }",
  "function constructorFirstFault() returns (Row) { return Row(failWord(), truth(false)); }",
  "function constructorLaterFault() returns (Row) { return Row(side(7), badBool()); }",
  "function baseFault() returns (Bool) { return badMap()[truth(true)]; }",
  "function keyFault() returns (Bool) { return filled()[badBool()]; }",
  "function defaultFault() returns (Missing) { let m: mapping(Bool => Missing); return m[truth(true)]; }"
]
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String) (arguments : List SourceTypedRuntime.Value)
    (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"data bound resume {name}" (first.resume 300000)).observation
private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (label : String) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"data bound prefix changed {label}"
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"data bound ordered cells changed {label}: {reprStr final.heap}"
private def constructor (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String) : IO DataConstructorInstantiation := do
  let signature ← match compiled.sourceProgram.signatures.dataTypes.filter (·.name == name) with
    | [signature] => pure signature | _ => throw (IO.userError "data bound nominal signature missing")
  let selected ← match signature.constructors with
    | [selected] => pure selected | _ => throw (IO.userError "data bound constructor missing")
  pure ⟨selected.id, [], selected.payloadTypes, .nominal signature.id []⟩
private def faultBinder (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
  let specialized ← SourceCoreUnifiedCorpusSupport.get "data bound fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == "gap") with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "data bound exact fault binder missing")

/-- The real cached named call supplies the base. The actual retained member
branch generator selects both fields, with the same complete native store. -/
private def retainedMembers (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "row"
  let entry ← match compiled.indexed.find? key with
    | some entry => pure entry | none => throw (IO.userError "data bound member entry missing")
  let baseCode ← SourceCoreUnifiedCorpusSupport.get "data bound actual named base"
    (SourceCoreCallableIndexedPrograms.assembleCall compiled.indexed.ancestry compiled.indexed.secondPass.closures key ⟨.unit, LanguageResult.success .unit⟩)
  let specialized ← SourceCoreUnifiedCorpusSupport.get "data bound member retained base"
    (SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan key)
  let original ← match specialized.function.typedBody.nodes.findSome? fun
    | .expression node => match node.form with | .constructor .. => some node | _ => none
    | _ => none with
    | some node => pure node | none => throw (IO.userError "data bound member source constructor missing")
  let baseline := Core.runStateful 300000 (.initial baseCode [] [])
  let baselineStore ← match baseline with
    | .done (.inRight .word _) store => pure store
    | other => throw (IO.userError s!"data bound member actual base failed: {reprStr other}")
  for (position, result, raw, expected) in [(0, Ty.word, TypeSystem.Ty.word, Value.word (Word.ofNatModulo 7)), (1, Ty.bool, TypeSystem.Ty.bool, Value.bool false)] do
    let member : ExpressionNode := {original with id := ⟨⟨original.id.occurrence.owner, 100000 + position⟩⟩, type := raw, form := .member original.id (toString position) position}
    let values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked
    let (identity, branches) ← SourceCoreUnifiedCorpusSupport.get "data bound member actual branches"
      (SourceCoreCompatibleDataExpressions.memberBranches values member original.type result position)
    let code := SourceCoreDataExpressions.member identity result branches baseCode
    let native ← SourceCoreUnifiedCorpusSupport.get "data bound member actual Core checker"
      (SourceCoreGeneralEntry.NativeEntry.compile compiled.indexed.layouts.definitions [] result code)
    SourceCoreUnifiedCorpusSupport.assertTrue (entry.native.resultType == .namedData identity)
      "data bound member lost base nominal type"
    for fuel in [0, 43, 300000] do
      let first ← SourceCoreUnifiedCorpusSupport.get "data bound member native call" (native.run [] fuel)
      let completed := match first.checkpoint? with | some checkpoint => checkpoint.resume 300000 | none => first
      match completed.observation with
      | .succeeded actual store =>
        SourceCoreUnifiedCorpusSupport.assertTrue (actual == expected && reprStr store == reprStr baselineStore)
          "data bound member changed selected value or named effect store"
      | other => throw (IO.userError s!"data bound member native result failed: {reprStr other}")

def run : IO Unit := do
  let names := ["single", "row", "nominalKey", "productKey", "duplicate", "baseIndex", "lazyIndex", "operatorParent",
    "constructorFirstFault", "constructorLaterFault", "baseFault", "keyFault", "defaultFault"]
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive named data bounds" content names
  let box ← constructor compiled "Box"
  let row ← constructor compiled "Row"
  let key ← constructor compiled "Key"
  let missing ← constructor compiled "Missing"
  let duplicate : SourceTypedRuntime.Value := .mapping (.product .bool .bool) .bool
    [(.product (.bool true) (.bool false), .bool false), (.product (.bool true) (.bool false), .bool true)]
  let filled : SourceTypedRuntime.Value := .mapping .bool .bool [(.bool true, .bool true)]
  let empty : SourceTypedRuntime.Value := .mapping .bool .bool []
  let successes : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("single", [], .constructed box [.bool true], [(.bool, some (.bool true)), (.bool, some (.bool true))]),
    ("row", [], .constructed row [w 7, .bool false], [(.word, some (w 7)), (.word, some (w 7)), (.bool, some (.bool false)), (.bool, some (.bool false))]),
    ("nominalKey", [], .bool false, [(.mapping key.resultType .bool, some (.mapping key.resultType .bool [])), (.bool, some (.bool true)), (.bool, some (.bool true))]),
    ("productKey", [], .bool false, [(.mapping (.product .bool .bool) .bool, some (.mapping (.product .bool .bool) .bool [])), (.bool, some (.bool true)), (.bool, some (.bool true)), (.bool, some (.bool false)), (.bool, some (.bool false))]),
    ("duplicate", [duplicate], .bool false, [(.mapping (.product .bool .bool) .bool, some duplicate), (.bool, some (.bool true)), (.bool, some (.bool true)), (.bool, some (.bool false)), (.bool, some (.bool false))]),
    ("baseIndex", [], .bool true, [(.mapping .bool .bool, some filled), (.bool, some (.bool true)), (.bool, some (.bool true))]),
    ("lazyIndex", [], .bool false, [(.mapping .bool .bool, some empty), (.bool, some (.bool true)), (.bool, some (.bool true))]),
    ("operatorParent", [], .bool false, [(.mapping .bool .bool, some filled), (.bool, some (.bool true)), (.bool, some (.bool true))])]
  let failures := ["constructorFirstFault", "constructorLaterFault", "baseFault", "keyFault", "defaultFault"]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (w 819)⟩]}
  let wordGap ← faultBinder compiled "failWord"
  let boolGap ← faultBinder compiled "badBool"
  let mapGap ← faultBinder compiled "badMap"
  let completed ← successes.mapM fun test => finish compiled test.1 test.2.1 300000 initial
  let failed ← failures.mapM fun name => finish compiled name [] 300000 initial
  for fuel in [0, 43, 300000] do
    for (test, baseline) in successes.zip completed do
      let (name, arguments, expected, expectedCells) := test
      let observation ← finish compiled name arguments fuel initial
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr observation == reprStr baseline)
        s!"data bound full resume observation changed {name}"
      match observation with
      | .done actual final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr expected) s!"data bound result changed {name}"
        cells initial final expectedCells name
        SourceCoreUnifiedCorpusSupport.assertTrue (final.isDeeplySafe 500 compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.plan)
          s!"data bound source heap not deeply safe {name}"
      | other => throw (IO.userError s!"data bound {name}: {reprStr other}")
    for (name, baseline) in failures.zip failed do
      let observation ← finish compiled name [] fuel initial
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr observation == reprStr baseline)
        s!"data bound full fault resume observation changed {name}"
      match observation with
      | .fault (.uninitializedLocal actual) final =>
        let expectedId := if name == "constructorFirstFault" then wordGap else if name == "baseFault" then mapGap else boolGap
        SourceCoreUnifiedCorpusSupport.assertTrue (actual == expectedId) "data bound fault lost source binder"
        let expectedCells := match name with
          | "constructorFirstFault" => [(.word, some (w 5)), (.word, none)]
          | "constructorLaterFault" => [(.word, some (w 7)), (.word, some (w 7)), (.word, some (w 19)), (.bool, none)]
          | "baseFault" => [(.word, some (w 23)), (.word, none)]
          | _ => [(.mapping .bool .bool, some filled), (.word, some (w 19)), (.bool, none)]
        cells initial final expectedCells name
      | .fault (.typeMismatch raw none) final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (name == "defaultFault" && raw == missing.resultType)
          "data bound missing default lost raw nominal metadata"
        cells initial final [(.mapping .bool missing.resultType, some (.mapping .bool missing.resultType [])), (.bool, some (.bool true)), (.bool, some (.bool true))] name
      | other => throw (IO.userError s!"data bound fault {name}: {reprStr other}")
  retainedMembers compiled
  IO.println "recursive named data bounds: original strict children, inclusive single pack, constructors/member/index, raw metadata, first lookup/effects/faults and resume GREEN"
end Tests.SourceCoreRecursiveNamedDataExpressionBounds
