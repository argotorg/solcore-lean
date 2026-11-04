import Solcore.Frontend.SourceCoreRawMetadata
import Solcore.Frontend.ProgramChecking
import Solcore.Frontend.SourceCoreStageCodebook
import Solcore.Frontend.SourceCoreStageContracts
import Solcore.Core.FuelResumptionProperties
import Solcore.Core.TaggedFunction

/-!
# Stage contract tests

Stage codebooks, stage contracts and raw metadata, kept small because they assert what they do not import.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreRawMetadata
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreRawMetadata.Registry.mk
#check_failure Solcore.Frontend.SourceCoreRawMetadata.Inserted.mk
#check_failure fun (registry : Solcore.Frontend.SourceCoreRawMetadata.Registry) =>
  { registry with metadataValues := [] }

/-! Authenticated raw metadata retains stage wrappers that are invisible to
runtime type compatibility. No executable source value or Core capability is
registered. Public consumer observations are tested in a separate module. -/

set_option autoImplicit false

namespace Tests.SourceCoreRawMetadata

open Solcore Solcore.Frontend SourceInference SourceCoreRawMetadata

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "enum Box<T> { Box(T) }",
    "enum Pair<A, B> { Pair(A, B) }",
    "enum Tree { Leaf(Word), Branch(Tree, Tree) }",
    "function main() returns (Word) { return 7; }"
  ] }] }

private def checked : IO CheckedProgram :=
  match checkProgram workspace with
  | .ok program => pure program
  | .error error => throw (IO.userError s!"raw metadata fixture failed checking: {reprStr error}")

private def data (program : CheckedProgram) (name : String) : IO ProgramDataSignature :=
  match program.signatures.dataTypes.filter (·.name == name) with
  | [signature] => pure signature
  | _ => throw (IO.userError s!"raw metadata data signature missing: {name}")

private def metadata (signature : ProgramDataSignature) (arguments : List TypeSystem.Ty)
    (index : Nat := 0) : IO DataConstructorInstantiation := do
  let constructor ← match signature.constructors[index]? with
    | some constructor => pure constructor
    | none => throw (IO.userError "raw metadata constructor missing")
  let substitution : TypeSystem.ParameterSubstitution := signature.parameters.zip arguments
  pure ⟨constructor.id, substitution, constructor.payloadTypes.map substitution.apply,
    .nominal signature.id arguments⟩

private def inserted (registry : Registry) (type : TypeSystem.Ty) (metadata : Metadata) :
    IO (Inserted registry type metadata) :=
  match registry.intern type metadata with
  | .ok inserted => pure inserted
  | .error error => throw (IO.userError s!"raw metadata insertion failed: {reprStr error}")

example (before : Registry) (expected : TypeSystem.Ty) (metadata : Metadata)
    (accepted : Inserted before expected metadata) :
    accepted.registry.lookup accepted.id = some metadata := accepted.reconstruct

example (before : Registry) (expected : TypeSystem.Ty) (metadata : Metadata)
    (accepted : Inserted before expected metadata) :
    runtimeType expected = runtimeType metadata.type := accepted.runtime_compatible

example (before : Registry) (expected : TypeSystem.Ty) (metadata : Metadata)
    (accepted : Inserted before expected metadata) (oldId : Core.Word) (oldMetadata : Metadata)
    (oldFound : before.lookup oldId = some oldMetadata) :
    accepted.registry.lookup oldId = some oldMetadata := accepted.preserves.lookup oldFound

example (registry : Registry) (left right : Core.Word) (a b : Metadata)
    (leftFound : registry.lookup left = some a) (rightFound : registry.lookup right = some b) :
    (left == right) = decide (a = b) := registry.word_equality_iff leftFound rightFound

example : idAt? (Core.wordModulus - 1) = none := by
  simp [idAt?, Core.Word.ofNat?, Core.wordModulus]

def run : IO Unit := do
  let program ← checked
  let box ← data program "Box"
  let pair ← data program "Pair"
  let tree ← data program "Tree"
  let ordinaryBox ← metadata box [.word]
  let stagedBox ← metadata box [.comptime .word]
  let ordinary : Metadata := .proxy .word
  let staged : Metadata := .proxy (.comptime .word)
  let registry ← match prepare program.signatures [ordinary, .constructor ordinaryBox, ordinary] with
    | .ok registry => pure registry
    | .error error => throw (IO.userError s!"static metadata preparation failed: {reprStr error}")
  assertTrue (registry.length == 2 && registry.staticLength == 2) "static metadata did not deduplicate in discovery order"
  let ordinaryId ← match registry.id? ordinary with
    | some id => pure id
    | none => throw (IO.userError "static proxy ID missing")
  assertTrue (ordinaryId.val == 1) "static metadata IDs are not one based"
  let stagedInsertion ← inserted registry (.proxy .word) staged
  let extended := stagedInsertion.registry
  assertTrue (stagedInsertion.id.val == 3 && extended.staticLength == 2) "dynamic extension changed the static prefix"
  assertTrue (extended.lookup ordinaryId == some ordinary) "dynamic extension changed an old ID"
  assertTrue (extended.lookup stagedInsertion.id == some staged) "dynamic extension erased proxy raw identity"
  assertTrue (ordinaryId != stagedInsertion.id) "runtime-equivalent proxy identities collapsed"
  let repeated ← inserted extended (.comptime (.proxy .word)) staged
  assertTrue (repeated.registry.length == extended.length && repeated.id == stagedInsertion.id)
    "same raw metadata was assigned another slot"
  let nominalInsertion ← inserted repeated.registry (.nominal box.id [.word]) (.constructor stagedBox)
  assertTrue (nominalInsertion.registry.lookup nominalInsertion.id == some (.constructor stagedBox))
    "raw nominal substitution/payload/result metadata changed"
  let mappingRaw : Metadata := .mapping (.comptime .word) (.proxy (.comptime .word))
  let mappingInsertion ← inserted nominalInsertion.registry (.mapping .word (.proxy .word)) mappingRaw
  assertTrue (mappingInsertion.registry.lookup mappingInsertion.id == some mappingRaw) "mapping raw header changed"
  assertTrue (mappingInsertion.registry.staticLength == registry.staticLength) "static prefix grew during input extension"
  let recursive ← metadata tree [] 1
  discard <| inserted mappingInsertion.registry recursive.resultType (.constructor recursive)
  for forged in [
      { stagedBox with payloadTypes := [.bool] },
      { stagedBox with resultType := .nominal box.id [.bool] },
      { stagedBox with constructor := { stagedBox.constructor with constructorIndex := 99 } },
      { stagedBox with parameterSubstitution := stagedBox.parameterSubstitution ++ stagedBox.parameterSubstitution }] do
    assertTrue (!constructorAuthentic program.signatures forged) "forged constructor metadata authenticated"
    match registry.intern forged.resultType (.constructor forged) with
    | .error (.invalidConstructor _) => pure ()
    | _ => throw (IO.userError "forged metadata was interned")
  let pairMetadata ← metadata pair [.word, .bool]
  let reordered := {pairMetadata with parameterSubstitution := pairMetadata.parameterSubstitution.reverse}
  assertTrue (!constructorAuthentic program.signatures reordered) "constructor substitution order was ignored"
  let limited ← match prepare program.signatures [ordinary] { maxEntries := 1 } with
    | .ok registry => pure registry
    | .error error => throw (IO.userError s!"one-entry registry failed: {reprStr error}")
  discard <| inserted limited (.proxy .word) ordinary
  match limited.intern (.proxy .word) staged with
  | .error (.entryBudgetExhausted 1) => pure ()
  | _ => throw (IO.userError "distinct metadata bypassed the registry budget")
  match limited.intern (.proxy .bool) staged with
  | .error (.runtimeTypeMismatch _ _) => pure ()
  | _ => throw (IO.userError "metadata type validation did not precede budget rejection")
  assertTrue ((limited.lookup Core.Word.zero).isNone) "zero resolved as a metadata ID"
  assertTrue ((limited.lookup ⟨99, by decide⟩).isNone) "unregistered metadata ID resolved"
  assertTrue ((idAt? (Core.wordModulus - 1)).isNone) "metadata ID wrapped at the word modulus"
  IO.println "raw metadata static prefixes, authenticated extensions and exact identity GREEN"

end Tests.SourceCoreRawMetadata
end

section
-- leanmerge: from Solcore.Test.SourceCoreStageCodebook
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreStageCodebook.Entry.mk
#check_failure Solcore.Frontend.SourceCoreStageCodebook.Decision.mk
#check_failure Solcore.Frontend.SourceCoreStageCodebook.Table.mk
#check_failure fun (entry : Solcore.Frontend.SourceCoreStageCodebook.Entry) => { entry with id := Solcore.Core.Word.zero }

/-! Finite stage descriptor catalogs are independent of source function
identity. Contextual lambda instances, builtin exemptions, preargument stage
faults, and postargument full-arity faults retain their original metadata. -/

set_option autoImplicit false

namespace Tests.SourceCoreStageCodebook

open Solcore Solcore.Frontend SourceInference SourceCoreStageCodebook

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}", "impl Mark<Bool> {}",
    "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
    "function marked(comptime item: Word) returns (Word) { return item; }",
    "function namedFault(value: Word) returns (Word) { let f = marked; return f(value); }",
    "function lambdaFault(value: Word) returns (Word) {",
    " let f = lam(comptime item: Word) -> Word { return item; }; return f(value); }",
    "function tupleParameter() returns (Word) {",
    " let f = lam(value: (Word, Word)) -> Word { return 7; }; return f(1, 2); }",
    "function effectfulTuple() returns (comptime<Word>) {",
    " let trace: Word = 0; let f = lam(value: (Word, Word)) -> Word { return 7; };",
    " let bump = lam() -> Word { trace += 1; return trace; }; return f(bump(), bump()); }",
    "function polymorphic(flag: Bool) returns (Word, Bool) {",
    " let f = lam(item) { return item; }; return (f(1), f(flag)); }",
    "function nested(flag: Bool) returns (Word, Word) {",
    " let outer = lam(value) { keep(value); let inner = lam(item) { return keep(item); }; return inner(1); };",
    " return (outer(1), outer(flag)); }",
    "function builtin(value: Word) returns (integer) { let op = wordToInteger; return op(value); }"
  ] }] }

private def key (program : CheckedProgram) (name : String) : IO Key :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError s!"stage codebook fixture missing: {name}")

private def plan (program : CheckedProgram) (name : String) : IO Plan := do
  let key ← key program name
  let plan ← match SourceSpecializationWorklist.run program [⟨key.declaration, []⟩] 64 with
    | .ok (.complete plan) => pure plan
    | other => throw (IO.userError s!"stage codebook worklist failed: {reprStr other}")
  match SourceCompilationPlan.prepareExecutablePlanEvidence program plan with
  | .ok plan => pure plan
  | .error error => throw (IO.userError s!"stage codebook plan failed: {reprStr error}")

private def checkedCatalog (program : CheckedProgram) (plan : Plan) : IO SourceCoreDataCatalog.Checked := do
  let locals ← match SourceCompilationPlan.localLambdaCatalog plan with
    | .ok locals => pure locals
    | .error error => throw (IO.userError s!"stage codebook discovery failed: {reprStr error}")
  let sourceTypes := fun (source : TypedSource) => source.inputs.map (·.scheme.body) ++
    source.nodes.map (fun | .expression node => node.type | .statement node => node.type)
  let types := plan.specializations.flatMap (fun specialized => specialized.function.type ::
    specialized.function.inferredBodyType :: sourceTypes specialized.function.typedBody) ++
    locals.flatMap (fun candidate => sourceTypes (candidate.source.applySubstitution candidate.substitution))
  match SourceCoreDataCatalog.prepare program.signatures 512 (types.filter SourceCoreDataCatalog.closed).eraseDups with
  | .ok checked => pure checked
  | .error error => throw (IO.userError s!"stage codebook data catalog failed: {reprStr error}")

private def codebook (program : CheckedProgram) (plan : Plan) (checked : SourceCoreDataCatalog.Checked) : IO Table :=
  match prepare program plan checked with
  | .ok table => pure table
  | .error error => throw (IO.userError s!"stage codebook rejected: {reprStr error}")

private def lambdaEntry (table : Table) (caller : Key) (count : Nat) : IO Entry :=
  match table.entries.filter (fun entry => match entry.origin with
    | .lambda owner _ [] => decide (owner = caller) && entry.parameterCount == count
    | _ => false) with
  | [entry] => pure entry
  | _ => throw (IO.userError "stage codebook lambda missing/ambiguous")

private def row (table : Table) (caller : Key) (entry : Entry) (count : Nat) : IO Decision :=
  match table.decisions.filter (fun row => decide (row.caller = caller) && row.entry.id == entry.id && row.argumentCount == count) with
  | [row] => pure row
  | _ => throw (IO.userError "stage codebook decision missing/ambiguous")

private def accepted (answer : Except RuntimeError Unit) : Bool :=
  match answer with | .ok () => true | _ => false

private def arity (answer : Except RuntimeError Unit) (expected actual : Nat) : Bool :=
  match answer with
  | .error (.argumentArityMismatch observedExpected observedActual) =>
      observedExpected == expected && observedActual == actual
  | _ => false

example (table : Table) : (table.entries.map (·.id)).Nodup := table.idsUnique
example (table : Table) : (table.entries.map (·.origin)).Nodup := table.originsUnique
example (table : Table) : (table.decisions.map Decision.key).Nodup := table.decisionsUnique

example (row : Decision) (guard : SourceCoreStageContracts.Guard) (same : row.guard = some guard) :
    row.answer = SourceCompilationPlan.validateStagedCallableContract guard.sidecar.caller guard.node guard.arguments
      guard.contract.parameters guard.contract.stagedResult guard.contract.owner := row.exact_guard guard same

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"stage codebook source checking failed: {reprStr error}")
  for name in ["namedFault", "lambdaFault", "tupleParameter", "effectfulTuple", "polymorphic", "nested", "builtin"] do
    let plan ← plan program name
    let checked ← checkedCatalog program plan
    let table ← codebook program plan checked
    let owner ← key program name
    assertTrue (table.entries.all (fun entry => entry.id.val > 0)) "stage codebook minted a zero descriptor"
    assertTrue (table.entries.all (fun entry => (table.idAt? entry.origin) == some entry.id &&
      (table.entryAt? entry.id).isSome)) "stage codebook origin/ID lookup lost an entry"
    for row in table.decisions do
      assertTrue ((table.decisionAt? row.caller row.call row.entry.id).isSome)
        "stage codebook decision lookup lost an authenticated key"
    let indirectCalls := plan.specializations.foldl (fun total specialized => total +
      (specialized.function.typedBody.nodes.filter (fun
        | .expression { form := .call _ _ (.indirect _), .. } => true
        | _ => false)).length) 0
    assertTrue (table.decisionCount == indirectCalls * table.contractCount)
      "stage codebook omitted a callsite/contract combination"
    for function in BuiltinFunctionId.all do
      let builtin ← match table.idAt? (.builtin function) with
        | some id => match table.entryAt? id with
          | some entry => pure entry
          | none => throw (IO.userError "builtin descriptor ID missing")
        | none => throw (IO.userError "builtin descriptor origin missing")
      assertTrue (builtin.parameterCount == function.parameterTypes.length)
        "builtin descriptor lost parameter arity"
      assertTrue ((table.decisions.filter (fun row => row.entry.id == builtin.id)).all (fun row => accepted row.beforeArguments))
        "builtins acquired staged-argument checks absent from old indirect invocation"
    let locals ← match SourceCoreLocalPolymorphism.prepare checked plan with
      | .ok locals => pure locals
      | .error error => throw (IO.userError s!"local origin checking failed: {reprStr error}")
    for binding in locals.bindings do
      for candidate in binding.instances do
        assertTrue ((table.idAt? (.lambda candidate.origin.caller candidate.origin.initializer candidate.origin.substitution)).isSome)
          "stage codebook lost a full cumulative local lambda context"
    if name == "lambdaFault" || name == "namedFault" then
      let entry ← if name == "lambdaFault" then lambdaEntry table owner 1
        else do
          let target ← key program "marked"
          let id ← match table.idAt? (.named target) with
            | some id => pure id | none => throw (IO.userError "named marked contract missing")
          match table.entryAt? id with
          | some entry => pure entry | none => throw (IO.userError "named marked descriptor missing")
      let row ← row table owner entry 1
      assertTrue (match row.beforeArguments with
        | .error (.comptimeArgumentStageMismatch caller call index argument stage) =>
            decide (caller = owner ∧ call = row.call) && index == 0 && stage == .runtime &&
              (row.guard.bind (fun guard => guard.arguments.head?)) == some argument
        | _ => false) "stage codebook changed an exact before-arguments stage reason"
      assertTrue (accepted row.afterArguments) "equal full callable arity became rejected"
    if name == "tupleParameter" || name == "effectfulTuple" then
      let entry ← lambdaEntry table owner 1
      let row ← row table owner entry 2
      if name == "tupleParameter" then
        assertTrue (arity row.beforeArguments 0 1) "ordinary caller lost residual preargument arity fault"
      else assertTrue (accepted row.beforeArguments) "effectful staging acquired a premature arity fault"
      assertTrue (arity row.afterArguments 1 2) "callable application lost full postargument arity mismatch"
    if name == "nested" then
      let inner := table.entries.filter (fun entry => match entry.origin with
        | .lambda _ _ context => !context.isEmpty && entry.parameterCount == 1
        | _ => false)
      assertTrue (inner.length ≥ 4) "nested qualified contexts collapsed into a final source function type"
    assertTrue (match prepare program plan checked {maxContracts := 0} with
      | .error (.contractBudgetExhausted 0) => true | _ => false) "contract budget was ignored"
    assertTrue (match prepare program plan checked {maxDecisions := 0} with
      | .error (.decisionBudgetExhausted 0) => true | _ => false) "decision budget was ignored"
    assertTrue (match prepare program plan checked {} 0 with
      | .error .zeroFirstId => true | _ => false) "zero descriptor space was accepted"
    assertTrue (match prepare program plan checked {} Core.wordModulus with
      | .error (.contractIdSpaceExhausted _) => true | _ => false) "word descriptor allocation wrapped"
    let shifted ← match prepare program plan checked {} 100 with
      | .ok shifted => pure shifted
      | .error error => throw (IO.userError s!"shifted descriptor space failed: {reprStr error}")
    assertTrue ((shifted.entries.head?.map (·.id.val)) == some 100)
      "stage descriptor allocation reused a source named-identity number"
    assertTrue ((table.entryAt? Core.Word.zero).isNone) "forged zero descriptor acquired a contract"

end Tests.SourceCoreStageCodebook
end

section
-- leanmerge: from Solcore.Test.SourceCoreStageContracts
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreStageContracts.Sidecar.mk
#check_failure Solcore.Frontend.SourceCoreStageContracts.Contract.mk
#check_failure Solcore.Frontend.SourceCoreStageContracts.Guard.mk
#check_failure fun (sidecar : Solcore.Frontend.SourceCoreStageContracts.Sidecar) => { sidecar with caller := sidecar.caller }
#check_failure fun (contract : Solcore.Frontend.SourceCoreStageContracts.Contract) => { contract with stagedResult := false }

/-! Parsed, checked callable contracts retain old stage decisions, including
accepted programs whose indirect invocation faults before evaluating arguments.
Native checks distinguish callee effects, skipped argument effects, and callee
failure priority. The whole source compiler routing is a separate owner. -/

set_option autoImplicit false

namespace Tests.SourceCoreStageContracts

open Solcore Solcore.Frontend SourceInference SourceCoreStageContracts

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "function markedEffects(comptime seed: Word) returns (comptime<Word>) {",
    " let total: Word = seed; let table: mapping(Word => Word);",
    " let bump = lam(comptime delta: Word) -> Word { total += delta; table[0] = total; return table[0]; };",
    " return bump(3); }",
    "function markedClosureClosed() returns (Word) {",
    " let f = lam(comptime value: Word) -> Word { return value; }; return f(21); }",
    "function markedClosureRuntime(value: Word) returns (Word) {",
    " let f = lam(comptime item: Word) -> Word { return item; }; return f(value); }",
    "function markedGlobal(comptime value: Word) returns (Word) { return value; }",
    "function markedGlobalClosed() returns (Word) { let f = markedGlobal; return f(22); }",
    "function markedGlobalRuntime(value: Word) returns (Word) { let f = markedGlobal; return f(value); }",
    "function markedResult(comptime value: Word) returns (comptime<Word>) { return value; }",
    "function markedResultIndirectBlocked() returns (Word) { let f = markedResult; return f(23); }",
    "function markedResultIndirectStaged() returns (comptime<Word>) { let f = markedResult; return f(24); }",
    "function many(flag: Bool, value: Word) returns (Word) {",
    " let f = lam(comptime staged: Word, flag: Bool, comptime other: Word) -> Word { return staged; };",
    " return f(1, flag, value); }",
    "function polymorphic(flag: Bool) returns (Word, Bool) {",
    " let f = lam(item) { return item; }; return (f(1), f(flag)); }",
    "function tupleParameter() returns (Word) {",
    " let f = lam(value: (Word, Word)) -> Word { return 7; }; return f(1, 2); }"
  ] }] }

private def key (program : CheckedProgram) (name : String) : IO Key :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError s!"staging fixture missing: {name}")

private def plan (program : CheckedProgram) (name : String) : IO Plan := do
  let key ← key program name
  let source ← match SourceSpecializationWorklist.run program [⟨key.declaration, []⟩] 64 with
    | .ok (.complete plan) => pure plan
    | other => throw (IO.userError s!"staging worklist failed: {reprStr other}")
  match SourceCompilationPlan.prepareExecutablePlanEvidence program source with
  | .ok prepared => pure prepared
  | .error error => throw (IO.userError s!"staging preparation failed: {reprStr error}")

private def sidecar (program : CheckedProgram) (plan : Plan) (name : String) : IO Sidecar := do
  let key ← key program name
  match prepareSidecar plan key with
  | .ok sidecar => pure sidecar
  | .error error => throw (IO.userError s!"staging sidecar failed: {reprStr error}")

private def call (sidecar : Sidecar) : IO ExpressionNode :=
  match sidecar.source.nodes.filterMap (fun
    | .expression node@{ form := .call _ _ (.indirect _), .. } => some node
    | _ => none) with
  | [node] => pure node
  | _ => throw (IO.userError "staging fixture must contain one indirect call")

private def lambda (sidecar : Sidecar) : IO ExpressionNode :=
  match sidecar.source.nodes.filterMap (fun
    | .expression node@{ form := .lambda _ _ _, .. } => some node
    | _ => none) with
  | [node] => pure node
  | _ => throw (IO.userError "staging fixture must contain one lambda")

private def guard (sidecar : Sidecar) (contract : Contract) : IO Guard := do
  let node ← call sidecar
  match prepareGuard sidecar node.id contract with
  | .ok guard => pure guard
  | .error error => throw (IO.userError s!"staging guard preparation failed: {reprStr error}")

private def lambdaGuard (program : CheckedProgram) (name : String) : IO Guard := do
  let plan ← plan program name
  let sidecar ← sidecar program plan name
  let node ← lambda sidecar
  let contract ← match Contract.lambda sidecar node.id with
    | .ok contract => pure contract
    | .error error => throw (IO.userError s!"staging lambda contract failed: {reprStr error}")
  guard sidecar contract

private def namedGuard (program : CheckedProgram) (name target : String) : IO Guard := do
  let plan ← plan program name
  let sidecar ← sidecar program plan name
  let target ← key program target
  let contract ← match Contract.named plan target with
    | .ok contract => pure contract
    | .error error => throw (IO.userError s!"staging named contract failed: {reprStr error}")
  guard sidecar contract

private def calleeType : Core.Ty := Core.TaggedFunction.functionType .word .word

private def callee (failure : Bool) : Core.Expr :=
  .letE (.storeCell (.var 0) (.word (word 1)))
    (if failure then Core.LanguageResult.failure calleeType (.word (word 72))
     else Core.LanguageResult.success
       (Core.TaggedFunction.anonymous (.lambda .word (Core.LanguageResult.resultType .word)
         (Core.LanguageResult.success (.var 0)))))

/-- This is the argument/body portion, under the successful callee binder. -/
private def arguments : Core.Expr :=
  .letE (.storeCell (.var 1) (.word (word 99)))
    (Core.LanguageResult.success (.word (word 7)))

private def native (guard : Guard) (failure : Bool) : Core.Program := {
  resultType := Core.LanguageResult.resultType .word
  body := .letE (.newCell .word (.word (word 0)))
    (guard.lower .word (callee failure) arguments (fun _ => word 71))
}

private theorem native_typed (guard : Guard) (failure : Bool) :
    Core.HasType [] (native guard failure).body (Core.LanguageResult.resultType .word) := by
  apply Core.HasType.letE (Core.HasType.newCell Core.HasType.word)
  apply Guard.lower_hasType guard (fun _ => word 71) .word
  · apply Core.HasType.letE (Core.HasType.storeCell (.var rfl) .word)
    cases failure
    · exact Core.LanguageResult.success_hasType
        (Core.TaggedFunction.anonymous_hasType
          (.lambda .word (Core.LanguageResult.resultType_wellFormed .word)
            (Core.LanguageResult.success_hasType (.var rfl))))
    · exact Core.LanguageResult.failure_hasType
        (Core.TaggedFunction.functionType_wellFormed .word .word) .word
  · exact .letE (.storeCell (.var rfl) .word) (Core.LanguageResult.success_hasType .word)

example (guard : Guard) :
    SourceStageAnalysis.FunctionAnalysisCertificate guard.sidecar.caller.function
      guard.sidecar.caller.stageAnalysis := guard.sidecar.certificate

example (guard : Guard) :
    SourceCompilationPlan.validateStagedCallableContract guard.sidecar.caller guard.node guard.arguments
      guard.contract.parameters guard.contract.stagedResult guard.contract.owner = guard.decision :=
  guard.decision_exact

example (guard : Guard) (failure : Bool) (fuel : Nat) :
    ((native guard failure).runStateful fuel).HasType (Core.LanguageResult.resultType .word) :=
  Core.well_typed_runStateful_has_type (Core.initial_state_has_type (native_typed guard failure)) fuel

example (guard : Guard) (failure : Bool) (spent additional : Nat) (checkpoint : Core.State)
    (exhausted : (native guard failure).runStateful spent = .outOfFuel checkpoint) :
    (Core.runStateful additional checkpoint).HasType (Core.LanguageResult.resultType .word) ∧
      Core.runStateful additional checkpoint = (native guard failure).runStateful (spent + additional) :=
  Core.well_typed_runStateful_resume_has_type
    (Core.initial_state_has_type (native_typed guard failure)) exhausted additional

private def checkNative (guard : Guard) (rejected : Bool) : IO Unit := do
  for failure in [false, true] do
    let program := native guard failure
    assertTrue program.check "stage guard failed native type checking"
    let value := if failure then Core.Value.inLeft .word (.word (word 72))
      else if rejected then .inLeft .word (.word (word 71)) else .inRight .word (.word (word 7))
    let heap := if failure || rejected then [Core.Value.word (word 1)] else [.word (word 99)]
    assertTrue (program.runStateful 100 == .done value heap)
      "stage guard changed callee effects, argument suppression, or callee failure priority"
    match program.runStateful 8 with
    | .outOfFuel checkpoint =>
        assertTrue (Core.runStateful 92 checkpoint == .done value heap)
          "stage guard changed on checkpoint resumption"
    | _ => throw (IO.userError "stage guard must suspend at fuel eight")

private def accepted (receipt : Guard) : Bool :=
  match receipt.decision with | .ok () => true | .error _ => false

private def argumentFault (receipt : Guard) (index : Nat) (argument : ExpressionId) : Bool :=
  match receipt.decision with
  | .error (.comptimeArgumentStageMismatch caller use actualIndex actualArgument actualStage) =>
      caller == receipt.sidecar.caller.key && use == receipt.node.id && actualIndex == index &&
      actualArgument == argument && actualStage == .runtime
  | _ => false

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"staging fixture checking failed: {reprStr error}")
  for name in ["markedEffects", "markedClosureClosed"] do
    let receipt ← lambdaGuard program name
    assertTrue (accepted receipt && receipt.contract.parameterStages == [true])
      "closed/effectful staged callable changed its existing accepted guard"
    checkNative receipt false
  for name in ["markedClosureRuntime", "many"] do
    let receipt ← lambdaGuard program name
    let expectedIndex := if name == "many" then 2 else 0
    let expectedArgument ← match receipt.arguments[expectedIndex]? with
      | some argument => pure argument
      | none => throw (IO.userError "staging fixture missing its failing argument")
    assertTrue (argumentFault receipt expectedIndex expectedArgument)
      "staging argument fault lost original caller, site, index, argument, or stage"
    if name == "many" then
      assertTrue (receipt.contract.parameterStages == [true, false, true])
        "staging contract flattened arbitrary parameter arity"
    checkNative receipt true
  for (name, target) in [("markedGlobalClosed", "markedGlobal"), ("markedResultIndirectStaged", "markedResult")] do
    let receipt ← namedGuard program name target
    assertTrue (accepted receipt) "accepted named staged contract became rejected"
    checkNative receipt false
  let runtime ← namedGuard program "markedGlobalRuntime" "markedGlobal"
  let argument ← match runtime.arguments.head? with
    | some argument => pure argument
    | none => throw (IO.userError "named staging fixture lost its argument")
  assertTrue (argumentFault runtime 0 argument) "named stage argument fault changed"
  checkNative runtime true
  let result ← namedGuard program "markedResultIndirectBlocked" "markedResult"
  assertTrue (match result.decision with
    | .error (.comptimeResultStageMismatch caller use owner stage) =>
        caller == result.sidecar.caller.key && use == result.node.id && owner == result.contract.owner && stage == .deferred
    | _ => false) "named staged result fault changed"
  checkNative result true
  let malformed := { result.sidecar.plan with specializations := result.sidecar.plan.specializations.map fun specialized =>
    if specialized.key == result.sidecar.caller.key then
      { specialized with stageAnalysis := { expressions := [], binders := [] } }
    else specialized }
  assertTrue (match prepareSidecar malformed result.sidecar.caller.key with
    | .error _ => true | _ => false) "edited caller stage table acquired a sealed receipt"
  assertTrue (match prepareGuard runtime.sidecar runtime.node.id result.contract with
    | .error .planMismatch => true | _ => false) "contract from another plan passed caller authentication"
  let lambdaReceipt ← lambdaGuard program "markedClosureClosed"
  let notCall ← lambda lambdaReceipt.sidecar
  assertTrue (match prepareGuard lambdaReceipt.sidecar notCall.id lambdaReceipt.contract with
    | .error (.expectedIndirectCall _) => true | _ => false)
    "lambda occurrence was accepted as a callsite"
  let tuple ← lambdaGuard program "tupleParameter"
  assertTrue (match tuple.decision with
    | .error (.argumentArityMismatch expected actual) => expected == 0 && actual == 1
    | _ => false) "one tuple parameter and two source arguments lost the existing preargument arity fault"
  checkNative tuple true
  let polymorphicPlan ← plan program "polymorphic"
  let polymorphicSidecar ← sidecar program polymorphicPlan "polymorphic"
  let polyLambda ← lambda polymorphicSidecar
  assertTrue (match Contract.lambda polymorphicSidecar polyLambda.id with
    | .error (.openLambda _) => true | _ => false)
    "open lambda metadata was projected without an authenticated local context"
  let data ← match SourceCoreDataCatalog.prepare program.signatures 64 [.word, .bool] with
    | .ok data => pure data
    | .error error => throw (IO.userError s!"staged polymorphic catalog failed: {reprStr error}")
  let catalog ← match SourceCoreLocalPolymorphism.prepare data polymorphicPlan with
    | .ok catalog => pure catalog
    | .error error => throw (IO.userError s!"staged polymorphic instances failed: {reprStr error}")
  let binding ← match catalog.bindings.filter (·.binder.name == "f") with
    | [binding] => pure binding
    | _ => throw (IO.userError "staged polymorphic binding missing")
  assertTrue (binding.instances.length == 2) "staged polymorphic fixture lost its Word/Bool contexts"
  for candidate in binding.instances do
    let prepared ← match SourceCoreLocalEvidence.prepare program polymorphicPlan candidate with
      | .ok prepared => pure prepared
      | .error error => throw (IO.userError s!"staged local context failed: {reprStr error}")
    let contract ← match Contract.contextualLambda polymorphicSidecar prepared polyLambda.id with
      | .ok contract => pure contract
      | .error error => throw (IO.userError s!"staged contextual lambda failed: {reprStr error}")
    let expectedParameter ← match candidate.origin.substitution.apply binding.binder.scheme.body with
      | .function parameter _ => pure parameter
      | _ => throw (IO.userError "staged local instance lost its function type")
    assertTrue (contract.parameters.map (·.scheme.body) == [expectedParameter]
      && contract.parameterStages == [false]) "staged contextual contract lost its exact concrete parameter"
    assertTrue (match Contract.contextualLambda lambdaReceipt.sidecar prepared notCall.id with
      | .error (.contextualCallerMismatch _) => true | _ => false)
      "local context from another caller acquired a stage contract"

end Tests.SourceCoreStageContracts
end
