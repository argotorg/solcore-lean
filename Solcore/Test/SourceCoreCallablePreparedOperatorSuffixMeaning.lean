import Solcore.SourceSemantics.CoreLowering.CallablePreparedOperatorSuffixMeaning
import Solcore.Test.SourceCoreCallablePreparedMethodRuntimeMeaning

/-! Selected raw operator traces and selected output paths are the source
preservation boundary. Runtime fixtures exercise actual public compilation,
nonempty ordered suffixes and first/later faults with complete stores. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000
namespace Tests.SourceCoreCallablePreparedOperatorSuffixMeaning
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap CoreProof ReadOnly CompatiblePayload CallableIndexedHistory
open CallablePreparedOperatorSuffixMeaning
open SourceCompilerFeatureSupport (get require)

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure CallablePreparedOperatorSuffixMeaning.Method.ordinary

section Actual
open CallablePreparedMethodRuntimeMeaning
variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  {compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code}
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {sourceBody : Dynamic.BodyInstance} {dictionary : Dynamic.EvidenceEnvironment}
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

variable (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
  (profile : CallablePreparedMethodRuntimeMeaning.Profile compiled values ambient sourceBody dictionary administrative registry faults)
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : SourceSemantics.Program) {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (diagnostics.reasonAt named.signature.key id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((diagnostics.reasonAt named.signature.key id).add tag))
  (escaped : faults .controlEscapedFunction compiled.own.table.escapedReason)
  {callerSource : TypedSource} {callerContext : SourceSemantics.Context}
  {callerEvidence : Dynamic.EvidenceEnvironment} {callerSolved : List SolvedRequirement}
  {callerReasonAt : ExpressionId → Word} {readFuel : Nat}
  (callerValid : CompatibleRuntimeContextValidity.Valid callerSolved callerContext callerEvidence)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (callerReasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((callerReasonAt id).add tag))
  {checkedProgram : CheckedProgram} {project : CallableCoercionExpressionCertificates.Projector}
  {caller : SourceSpecialization.SpecializedFunction} {compilation : SourceCoreFunctions.Context}
  {child : SourceCoreEvidence.Child} {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {policy : SourceCoreFunctions.CallablePolicy} {node : ExpressionNode} {output : SourceCoreBasic.LoweredExpr}
  (receipt : CallablePreparedMethodSelection.Operator checkedProgram project caller compilation child fuel
    callerSource scope id callerReasonAt policy node output)

variable (alignment : OperatorAlignment (named := named) (sourceBody := sourceBody) (dictionary := dictionary) receipt)
  (selected : OperatorSource receipt)
  (selection : Dynamic.OperatorMethodSelected program callerContext callerEvidence selected.traitName selected.methodName
    receipt.requirements sourceBody dictionary)
  (children : DataExpressionSequence.Tree callerSource
    (CompatibleExpressionBuiltinRuntime.Certificate readFuel values callerSource callerContext callerSolved callerReasonAt)
    scope receipt.arguments (named.inputs.map (fun binding => binding.1.scheme.body)) receipt.loweredArguments)
  (nativeTypes : receipt.loweredArguments.map (·.type) = named.inputs.map Prod.snd)


variable {methods : Methods (prepared := prepared) (values := values) (ambient := ambient)
    (registry := registry) (faults := faults) (program := program) (context := callerContext) (evidence := callerEvidence)}
  (suffixUninitialized : ∀ method ∈ methods, ∀ id location,
    faults (.uninitializedLocation location) (method.diagnostics.reasonAt method.named.signature.key id))
  (suffixMissing : ∀ method ∈ methods, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((method.diagnostics.reasonAt method.named.signature.key id).add tag))
  (suffixEscaped : ∀ method ∈ methods, faults .controlEscapedFunction method.compiled.own.table.escapedReason)
  {ξ : Renaming} {calls : List CallableCoercionSpine.Call}
  (emitted : Emitted checkedProgram project compilation caller receipt.available scope node policy ξ receipt.operand methods output calls)
  (steps : methods.map (·.step) = node.coercions)
  (chain : CallableCoercionPathMeaning.ChainFor Method.row sourceBody.resultType receipt.operand.type methods node.type output.type)


include extension faithful observations functionTypes uninitialized missing escaped callerValid callerUninitialized callerMissing
  children nativeTypes profile alignment selected selection suffixUninitialized suffixMissing suffixEscaped emitted steps chain in
/-- The original raw operator and every selected output conversion are closed
by their actual runtime trees. No child or body execution law is an input. -/
theorem actual_preserves {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap}
    {store : Store} {callerEnvironment canonical : Environment}
    {callerAdministrative actualContext : Core.Context} {sourceEnvironment : Dynamic.Environment}
    {outcome : Dynamic.ExpressionOutcome}
    (installed : CallablePreparedMethodRuntimeMeaning.Installed compiled (sourceBody := sourceBody) (administrative := administrative)
      functions mapping world before store callerEnvironment)
    (located : installed.globalIndex = ξ (scope.length + compilation.administrativePrefix + receipt.native.index))
    (suffixEntry : Entry methods functions callerEnvironment mapping world before store)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      callerAdministrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before callerContext.locals sourceEnvironment)
    (layout : EnvironmentsAgree ξ canonical callerEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world callerEnvironment actualContext ambient.definitions)
    (unique : NodeOccurrencesUnique callerSource)
    (execution : CallablePreparedOperatorSuffixMeaning.Trace (sourceBody := sourceBody) (dictionary := dictionary) (program := program) (receipt := receipt) (methods := methods) sourceEnvironment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program callerContext callerEvidence callerSource sourceEnvironment before id outcome after ∧
      Evaluates callerEnvironment store (output.expression.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods functions callerEnvironment finalMap finalWorld after finalStore) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame
        installed.frameLocation installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.ancestry.graph.inputs prepared.ancestry.graph.table
        prepared.ancestry.layout.frame finalMap finalStore installed.records := by
  exact CallablePreparedOperatorSuffixMeaning.preserves
    (compiled := compiled) (profile := profile) (functions := functions) (extension := extension)
    (program := program) (faithful := faithful) (observations := observations) (functionTypes := functionTypes)
    (uninitialized := uninitialized) (missing := missing) (escaped := escaped) (callerValid := callerValid)
    (callerUninitialized := callerUninitialized) (callerMissing := callerMissing) (receipt := receipt) (alignment := alignment)
    (selected := selected) (selection := selection) (children := children) (nativeTypes := nativeTypes)
    (suffixUninitialized := suffixUninitialized) (suffixMissing := suffixMissing) (suffixEscaped := suffixEscaped) (emitted := emitted)
    (steps := steps) (chain := chain)
    installed located suffixEntry environments heaps locals layout actualTyped unique execution
include extension faithful observations functionTypes uninitialized missing escaped callerValid callerUninitialized callerMissing
  children nativeTypes profile alignment selected selection suffixUninitialized suffixMissing suffixEscaped emitted steps chain in
/-- Completed output code supplies the original measured operand and each
actual suffix body. Reflection does not require a source completion. -/
theorem actual_reflects {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
    {store finalStore : Store} {callerEnvironment canonical : Environment}
    {callerAdministrative actualContext : Core.Context} {sourceEnvironment : Dynamic.Environment}
    {value : Value} {size : Nat}
    (installed : CallablePreparedMethodRuntimeMeaning.Installed compiled (sourceBody := sourceBody) (administrative := administrative)
      functions mapping world before store callerEnvironment)
    (located : installed.globalIndex = ξ (scope.length + compilation.administrativePrefix + receipt.native.index))
    (suffixEntry : Entry methods functions callerEnvironment mapping world before store)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      callerAdministrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before callerContext.locals sourceEnvironment)
    (layout : EnvironmentsAgree ξ canonical callerEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world callerEnvironment actualContext ambient.definitions)
    (completed : EvaluationSize size callerEnvironment store (output.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program callerContext callerEvidence callerSource sourceEnvironment before id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods functions callerEnvironment finalMap finalWorld after finalStore) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame
        installed.frameLocation installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.ancestry.graph.inputs prepared.ancestry.graph.table
        prepared.ancestry.layout.frame finalMap finalStore installed.records := by
  exact CallablePreparedOperatorSuffixMeaning.reflects_sized
    (compiled := compiled) (profile := profile) (functions := functions) (extension := extension)
    (program := program) (faithful := faithful) (observations := observations) (functionTypes := functionTypes)
    (uninitialized := uninitialized) (missing := missing) (escaped := escaped) (callerValid := callerValid)
    (callerUninitialized := callerUninitialized) (callerMissing := callerMissing) (receipt := receipt) (alignment := alignment)
    (selected := selected) (selection := selection) (children := children) (nativeTypes := nativeTypes)
    (suffixUninitialized := suffixUninitialized) (suffixMissing := suffixMissing) (suffixEscaped := suffixEscaped) (emitted := emitted)
    (steps := steps) (chain := chain)
    installed located suffixEntry environments heaps locals layout actualTyped completed

end Actual

abbrev original_suffix_children := @CallableCoercionSpine.Spine.renamed_completed_sized
abbrev original_stored_body := @CallablePreparedOperatorSuffixMeaning.Capture.completed_sized
abbrev actual_suffix_receipt := @CallablePreparedOperatorSuffixMeaning.actual_suffix

section Boundaries
variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {program : SourceSemantics.Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  (method : CallablePreparedOperatorSuffixMeaning.Method prepared values ambient registry faults program context evidence)

theorem full_dictionary : method.row.dictionary = method.dictionary := rfl

theorem same_full_runtime_ledger :
    method.profile.context.solvedRequirements = method.named.specialized.function.solvedRequirements :=
  method.profile.body.valid.ledger

theorem repeated_rows : ([method, method].map (fun row => row.row.dictionary)) = [method.dictionary, method.dictionary] := rfl

theorem original_selected : Dynamic.OperatorMethodSelected program context evidence "Coerce" "coerce"
    method.step.requirements method.sourceBody method.dictionary := method.selected

end Boundaries

private def content (mode : Nat) : String := String.intercalate "\n" [
  "trait Marker<T> {}", "trait Witness<T> {}",
  "impl Marker<(Word, Bool)> {}", "impl Witness<(Word, Bool)> {}",
  "impl Marker<Bool> {}", "impl Witness<Bool> {}",
  "trait Add<T> where T: Marker { function add(left: T, right: T) returns (T) where T: Witness; }",
  "trait Coerce<From, To> where From: Marker { function coerce(value: From) returns (To) where From: Witness; }",
  "impl Add<(Word, Bool)> where (Word, Bool): Marker { function add(left: (Word, Bool), right: (Word, Bool)) returns ((Word, Bool)) where (Word, Bool): Witness { let rawEffect: Word = 101; return right; } }",
  "impl Coerce<(Word, Bool), Bool> where (Word, Bool): Marker { function coerce(value: (Word, Bool)) returns (Bool) where (Word, Bool): Witness { let firstEffect: Word = 103; " ++
    (if mode == 1 then "let firstGap: Bool; return firstGap;" else "return true;") ++ " } }",
  "impl Coerce<Bool, Word> where Bool: Marker { function coerce(value: Bool) returns (Word) where Bool: Witness { let secondEffect: Word = 107; " ++
    (if mode == 2 then "let secondGap: Word; return secondGap;" else "return 19;") ++ " } }",
  "function root(a: Word, b: Bool) returns (Word) { " ++
    (if mode == 3 then "let rawGap: (Word, Bool);" else "let rawGap: (Word, Bool) = (a, b);") ++
    " let right: (Word, Bool) = (7, false); return rawGap + right; }"
]

private def inspect (cached : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let base := cached.indexed.base
  let root ← SourceCoreUnifiedCorpusSupport.key cached.sourceProgram "root"
  let named ← match base.functions.find? (·.signature.key == root) with
    | some value => pure value | none => throw (IO.userError "suffix actual root missing")
  let caller := named.specialized
  let program := cached.sourceProgram
  let representation := SourceCoreCompatibleFunctions.representation (.initial cached.compatible.checked) cached.compilationFuel
  let project := representation.expressions.projectType
  let policy : SourceCoreFunctions.CallablePolicy := {allowStaged := representation.allowStaged}
  let available ← get "suffix caller" (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions)
  let mut found := false
  for item in caller.function.typedBody.nodes do
    if let .expression node := item then
      if let .binary left operator right := node.form then
        let requirements ← match SourceCompilationPlan.ordinaryOwnedRequirements? node with
          | some value => pure value | none => throw (IO.userError "suffix requirement layout missing")
        if requirements.isEmpty then continue
        require (node.coercions.length == 2) "actual operator suffix length changed"
        let raw := CallableCoercionExpressionCertificates.rawNode node requirements
        let selected ← get "suffix raw operator selector"
          (SourceCompilationPlan.checkedBinaryOperatorMethod program caller raw available operator)
        let actual ← get "suffix raw fullrow" (SourceCompilationPlan.exactSpecialization base.plan selected.method.specialized.key)
        require (actual == selected.method.specialized) "raw method full row changed"
        let mut expectedTypes : List TypeSystem.Ty := []
        let mut indices : List Nat := []
        for step in node.coercions do
          let method ← get "suffix selected method" (SourceCompilationPlan.checkedCoercionMethod program caller node available step)
          let dictionary ← get "suffix full dictionary" (SourceCompilationPlan.coercionMethodRuntimeEvidence program caller node step method)
          let key ← get "suffix actual edge" (SourceCompilationPlan.exactCallKey base.plan caller.key node.id method.specialized.key)
          let complete ← get "suffix complete row" (SourceCompilationPlan.exactSpecialization base.plan key)
          let row ← match base.functions.zipIdx.filter (fun row => row.1.specialized == complete) with
            | [row] => pure row | _ => throw (IO.userError "suffix physical row missing")
          require (complete == method.specialized && dictionary.length == 3 && dictionary[0]? == dictionary[1]? &&
            dictionary[1]? != dictionary[2]? && dictionary.map SourceCompilationPlan.runtimeEvidenceGoal == complete.assumptions &&
            base.plan.specializations.reverse[row.2]? == some complete &&
            (cached.indexed.secondPass.closures[row.2]?).isSome && row.1.inputs.length == 1)
            "suffix full record/dictionary order/cache changed"
          expectedTypes := expectedTypes ++ [step.source, step.target]
          indices := indices ++ [row.2]
        require (expectedTypes == [.product .word .bool, .bool, .bool, .word] && indices.length == 2)
          "suffix raw endpoint order changed"
        let compilation : SourceCoreFunctions.Context := {
          plan := base.plan, owner := caller.key, globals := base.globals, administrativePrefix := 0, solvedRequirements := caller.function.solvedRequirements,
          internalReason := Word.ofNatModulo 29}
        let reasonAt := fun id : ExpressionId => Word.ofNatModulo (1000 + id.occurrence.index)
        let child : SourceCoreEvidence.Child := fun remaining source _ id _ => do
          if remaining != 37 then throw (.unsupportedExpression node.id node.form)
          let childNode ← match source.lookupExpression? id with
            | some value => pure value | none => throw (.unsupportedExpression node.id node.form)
          let type ← project (.occurrence id.occurrence) childNode.type
          pure ⟨type, .inLeft type (.word (reasonAt id))⟩
        let actual ← get "suffix actual lowering" (SourceCoreEvidence.lowerWithProjector program project caller compilation child
          37 caller.function.typedBody [] node.id reasonAt policy)
        let codes ← [left, right].mapM (fun id => get "suffix ordered operands" (child 37 caller.function.typedBody [] id reasonAt))
        let row ← match base.functions.zipIdx.filter (fun row => row.1.specialized == selected.method.specialized) with
          | [row] => pure row | _ => throw (IO.userError "operator physical row missing")
        let operand : SourceCoreBasic.LoweredExpr := ⟨row.1.signature.resultType,
          SourceCoreCalls.call row.1.signature row.2 (SourceCoreCalls.packArguments codes).expression compilation.internalReason⟩
        let expected ← get "suffix same emitter" (SourceCoreEvidence.applyCoercions program project compilation caller available [] node policy operand node.coercions)
        require (actual == some expected && Core.infer? (base.globals.map SourceCoreCalls.Signature.referenceType)
          expected.expression cached.indexed.layouts.definitions == some (LanguageResult.resultType expected.type))
          "suffix actual ordered emission/type changed"
        require ((SourceCoreEvidence.lowerWithProjector program project caller compilation child 36
          caller.function.typedBody [] node.id reasonAt policy).toOption.isNone) "suffix child fuel changed"
        let ledger := caller.function.solvedRequirements
        let first ← match ledger with | first :: _ => pure first | _ => throw (IO.userError "suffix full ledger empty")
        let extra := {first with
          id := ⟨(ledger.map (fun (row : SolvedRequirement) => row.id.index)).foldl max 0 + 1⟩,
          evidence := .assumption first.predicate}
        for complete in [extra :: ledger, ledger ++ [extra]] do
          let retained := {caller with function := {caller.function with solvedRequirements := complete}}
          require ((SourceCoreEvidence.lowerWithProjector program project retained {compilation with solvedRequirements := complete}
            child 37 caller.function.typedBody [] node.id reasonAt policy).toOption == some actual)
            "suffix unused full ledger changed selected rows"
        found := true
  require found "actual nonempty operator suffix missing"

private def execute (cached : SourceCoreUnifiedCompilation.Compiled) (root : SourceSpecialization.SpecializationKey)
    (fuel : Nat) : IO (SourceCoreUnifiedCompilation.Result cached) := do
  let first ← get "suffix start" (cached.run root [.word (Word.ofNatModulo 5), .bool true] 1024 fuel)
  get "suffix resume" (first.resume 300000)

private def expected_cells (mode : Nat) : List SourceTypedRuntime.Cell :=
  let word := fun value => SourceTypedRuntime.Value.word (Word.ofNatModulo value)
  let pairType := TypeSystem.Ty.product .word .bool
  let first := SourceTypedRuntime.Value.product (word 5) (.bool true)
  let second := SourceTypedRuntime.Value.product (word 7) (.bool false)
  let initial := [⟨.word, some (word 5)⟩, ⟨.bool, some (.bool true)⟩,
    ⟨pairType, if mode == 3 then none else some first⟩, ⟨pairType, some second⟩]
  if mode == 3 then initial else
    let raw := initial ++ [⟨pairType, some first⟩, ⟨pairType, some second⟩, ⟨.word, some (word 101)⟩]
    let converted := raw ++ [⟨pairType, some second⟩, ⟨.word, some (word 103)⟩]
    if mode == 1 then converted ++ [⟨.bool, none⟩] else
      converted ++ [⟨.bool, some (.bool true)⟩, ⟨.word, some (word 107)⟩] ++
        (if mode == 2 then [⟨.word, none⟩] else [])

private def audit (mode : Nat) : IO Unit := do
  let program ← get "suffix source" (checkProgram {
    entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := content mode}]})
  let key ← SourceCoreUnifiedCorpusSupport.key program "root"
  let compiled ← get "suffix public compile" (SourceCoreCompiler.compileChecked program
    [.declaration key.declaration []] {specializationBudget := 512, compilationFuel := 1000})
  let cached ← match compiled.artifact? with | some value => pure value | none => throw (IO.userError "suffix cache absent")
  inspect cached
  let baseline ← execute cached key 300000
  let native ← match baseline.execution with | some value => pure value | none => throw (IO.userError "suffix native observation missing")
  let expectedGap := if mode == 1 then "firstGap" else if mode == 2 then "secondGap" else "rawGap"
  match baseline.observation with
  | .done value state =>
    require (reprStr state.heap == reprStr (expected_cells mode)) "suffix exact success heap changed"
    require (mode == 0 && reprStr value == reprStr (SourceTypedRuntime.Value.word (Word.ofNatModulo 19))) "suffix expected success changed"
    require ((state.heap.filterMap (fun cell => cell.value)).any (fun value => reprStr value == reprStr (SourceTypedRuntime.Value.word (Word.ofNatModulo 101))) &&
      (state.heap.filterMap (fun cell => cell.value)).any (fun value => reprStr value == reprStr (SourceTypedRuntime.Value.word (Word.ofNatModulo 103))) &&
      (state.heap.filterMap (fun cell => cell.value)).any (fun value => reprStr value == reprStr (SourceTypedRuntime.Value.word (Word.ofNatModulo 107)))) "suffix body effect missing"
  | .fault (.uninitializedLocal actual) state =>
    let gaps := cached.indexed.base.functions.flatMap (fun named =>
      (SourceCoreDataPlaces.declaredBinders named.specialized.function.typedBody).filter (·.name == expectedGap))
    let expected ← match gaps with | [binder] => pure binder.id | _ => throw (IO.userError "suffix exact fault binder missing")
    require (mode != 0 && actual == expected && reprStr state.heap == reprStr (expected_cells mode))
      s!"suffix first/later original fault changed: mode={mode}, actual={reprStr actual}, expected={reprStr expected}, heap={reprStr state.heap}"
    require (!(state.heap.filterMap (fun cell => cell.value)).any (fun value => reprStr value == reprStr (SourceTypedRuntime.Value.word (Word.ofNatModulo 107))) || mode == 2)
      "suffix executed a skipped body"
    if mode == 3 then
      require (!(state.heap.filterMap (fun cell => cell.value)).any (fun value => reprStr value == reprStr (SourceTypedRuntime.Value.word (Word.ofNatModulo 101))))
        "raw argument failure entered operator body"
  | _ => throw (IO.userError "suffix execution did not complete")
  for fuel in [0, 1, 31, 300000] do
    let actual ← execute cached key fuel
    let actualNative ← match actual.execution with | some value => pure value | none => throw (IO.userError "suffix resumed native missing")
    require (reprStr actual.observation == reprStr baseline.observation &&
      reprStr actualNative.completion.result.native.observation == reprStr native.completion.result.native.observation)
      "suffix full source/native ordered stores or resume changed"

def run : IO Unit := do
  for mode in [0, 1, 2, 3] do audit mode
  IO.println "operator output suffix: actual two-step source/native/full dictionary/first-later faults/ordered stores/resume GREEN"

end Tests.SourceCoreCallablePreparedOperatorSuffixMeaning
