import Solcore.SourceSemantics.CoreLowering.RecursiveNamedSelectedExpressionFactory
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Selected headers supply named validity at the real contextual compiler
and the unique body extractor. Constructor raw ranges remain explicit;
execution checks are separate from the source/static proofs. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedSelectedExpressions
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableAncestryPairedLookup
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open RecursiveNamedCatalogNativeContexts RecursiveNamedCatalogProfileFactory
open RecursiveGlobalInitializationMeaning RecursiveGlobalInitializationTyping
open RecursiveNamedExpressionCompilerCertificates RecursiveNamedCallSelectionCertificates
open CompatibleExpressionInstantiationLaws CompatibleSourceInstantiationClosure
open RecursiveNamedSelectedExpressionFactory

variable (cached : SourceCoreUnifiedCompilation.Compiled)
  {recipe : SourceCoreIndexedSession.Recipe}
  (recipeAccepted : SourceCoreIndexedSession.Recipe.prepare cached = .ok recipe)
  {nativeEntry : SourceCoreCallableIndexedPrograms.Entry cached.indexed.layouts}
  (member : nativeEntry ∈ cached.indexed.entries)
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  (definitions : ambient.definitions = cached.indexed.layouts.definitions)
  {headers : Inventory cached.indexed.ancestry values ambient.definitions program} {locations : Locations}
  {header : Header cached.indexed.ancestry values ambient.definitions program}
  (sameCache : header.compiled.closures = cached.indexed.secondPass.closures)
  (complete : Complete headers) (globals : header.globals = cached.indexed.base.globals.length)
  {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location}
  {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame}
  (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
    administrative actualContext actual ξ frameLocation current ghost)

variable {compilation : SourceCoreFunctions.Context} {expressionSyntax : ExpressionId → Prop}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}


include member definitions sameCache complete globals recipeAccepted entry in
theorem actual_extraction (diagnosticPolicy : AssignmentDiagnosticPolicy)
    {catalogSignatures : ProgramSignatures} {catalogFuel : Nat} {catalogTypes : List TypeSystem.Ty}
    {metadata : List SourceCoreCompatibleCatalog.Metadata} {limits : SourceCoreCompatibleCatalog.Limits} {contracts : Bool}
    (registered : SourceCoreCompatibleCatalog.prepare catalogSignatures catalogFuel catalogTypes metadata limits contracts = .ok values.checked)
    (prefixEq : compilation.administrativePrefix = 1) {tracked : Bool}
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy header.function.source invalidOperand)
    (readPolicy : header.policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      header.policy.lowerBinder header.function.source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked header.function.source scope binder)
    (allocationPolicy : header.policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator cached.indexed.ancestry.layout.frame header.globals
      (header.layouts.allocatorAt header.owner header.active header.onError)))
    {checkedProgram : CheckedProgram} {signatures : ProgramSignatures}
    {locals : SourceCoreLocalPolymorphism.Catalog} {parents : List SourceCoreLocalEvidence.Prepared}
    {assignmentTable : SourceCoreAssignmentFaultSites.Table} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
    {native : SourceCoreGeneralFunctions.CallableContext} {skipInitializer : Option ExpressionId}
    {caller : SourceSpecialization.SpecializedFunction}
    (policyExpression : header.policy.lowerExpression = SourceCoreGeneralFunctions.lowerContextualExpression
      checkedProgram header.representation signatures locals parents assignmentTable diagnostics compilation
      (some native) none skipInitializer)
    (sameLedger : compilation.solvedRequirements = header.solved)
    (admission : Admission header.function.source expressionSyntax)
    (coverage : Coverage headers compilation) (sourceTypes : SourceTypes headers header.context)
    (order : ∀ id callee arguments instantiation node, expressionSyntax id →
      header.function.source.lookupExpression? id = some node →
      node.form = .call callee arguments (.declaration instantiation) → Ordered compilation.plan instantiation)
    (ordinary : Ordinary header.function.source locals compilation.owner expressionSyntax)
    (callerSelected : SourceCompilationPlan.exactSpecialization compilation.plan compilation.owner = .ok caller)
    (callerClosed : caller.assumptions = [])
    (constructorRanges : ConstructorRanges header.function.source
      (fun id => expressionSyntax id ∨ CompatibleExpressionBuiltins.Syntax header.function.source id))
    (expressionRead : header.representation.expressions.readExpression =
      SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (expressionLower : header.representation.expressions.lowerRead =
      SourceCoreCompatibleDataExpressions.lowerRead header.readFuel values)
    (expressionLeaf : header.representation.expressions.leafLowerer =
      SourceCoreCompatibleDataExpressions.leafLowerer values)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy header.policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy header.policy values invalidProjection invalidUnary missingDefault)
    (syntaxTree : GenericImperativeFor.Syntax header.function.source expressionSyntax header.context
      (.statements true header.function.body) header.function.resultType)
    (sourceSignatures : header.context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations header.function.source (bodyScope header) header.context)
    (projection : values.checked.catalog.project header.function.resultType = .ok header.output)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (bodyScope header) header.function.body header.output header.reasonAt header.fellThrough header.escaped = .ok header.body)
    : Nonempty (Receipt diagnosticPolicy headers header compilation expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) := by
  exact RecursiveNamedSelectedExpressionFactory.extract
    (cached := cached) (recipeAccepted := recipeAccepted)
    (rows := RecursiveNamedCachedRows.rows cached) (cachedRows := RecursiveNamedCachedRows.exact_cache cached)
    (ordered := RecursiveNamedCachedRows.ordered cached) (member := member) (definitions := definitions)
    (sameCache := sameCache) (complete := complete) (globals := globals) (entry := entry)
    (diagnosticPolicy := diagnosticPolicy)
    (catalogSignatures := catalogSignatures)
    (catalogFuel := catalogFuel)
    (catalogTypes := catalogTypes)
    (metadata := metadata)
    (limits := limits)
    (contracts := contracts)
    (registered := registered)
    (prefixEq := prefixEq)
    (tracked := tracked)
    (factory := factory)
    (readPolicy := readPolicy)
    (binderPolicy := binderPolicy)
    (allocationPolicy := allocationPolicy)
    (checkedProgram := checkedProgram)
    (signatures := signatures)
    (locals := locals)
    (parents := parents)
    (assignmentTable := assignmentTable)
    (diagnostics := diagnostics)
    (native := native)
    (skipInitializer := skipInitializer)
    (caller := caller)
    (policyExpression := policyExpression)
    (sameLedger := sameLedger)
    (admission := admission)
    (coverage := coverage)
    (sourceTypes := sourceTypes)
    (order := order)
    (ordinary := ordinary)
    (callerSelected := callerSelected)
    (callerClosed := callerClosed)
    (constructorRanges := constructorRanges)
    (expressionRead := expressionRead)
    (expressionLower := expressionLower)
    (expressionLeaf := expressionLeaf)
    (assignments := assignments)
    (unaryPolicy := unaryPolicy)
    (syntaxTree := syntaxTree)
    (sourceSignatures := sourceSignatures)
    (declarations := declarations)
    (projection := projection)
    (accepted := accepted)

/-- The selected receipt still owns the diagnostic obligations. -/
theorem actual_profile {diagnosticPolicy : AssignmentDiagnosticPolicy} {faults : FunctionCalls.FaultRep}
    (receipt : Receipt diagnosticPolicy headers header compilation expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))
    (interpreted : receipt.extracted.diagnostics registry faults) :
    Nonempty (ProfileFor diagnosticPolicy headers header compilation header.readFuel expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults) :=
  ⟨receipt.profile interpreted⟩

/-- This is a source structural fact, independent of native code or execution. -/
theorem actual_header_context :
    header.context.typeVariables = [] ∧ header.context.residualTypeVariables = true :=
  RecursiveNamedSourceContextFacts.header_fields header

theorem old_false_excluded : header.context.residualTypeVariables ≠ false :=
  RecursiveNamedSourceContextFacts.header_not_false header


section Boundary
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def flexible : SourceSemantics.Context := (SourceSemantics.Context.ofSignatures signatures).withResidualTypeVariables

/-- Residual admission alone cannot fill the raw closure receipt. In particular,
an unused substitution row is not discarded by looking only at result types. -/
theorem unused_range_not_closed (parameter : TypeSystem.TypeParameterId) :
    ParameterSubstitution.RangeAdmissible flexible [(parameter, .variable ⟨37⟩)] ∧
    TypeSystem.ParameterSubstitution.apply [(parameter, .variable ⟨37⟩)] .word = .word ∧
    ¬ ClosedParameterRange [(parameter, .variable ⟨37⟩)] := by
  refine ⟨?_, rfl, ?_⟩
  · intro other replacement member
    cases List.mem_singleton.mp member
    exact TypeAdmissible.variableOfResidual (by
      simp [TypeParameterBindersWellFormed, flexible, Context.ofSignatures, Context.withResidualTypeVariables]) rfl ⟨37⟩
  · intro closed
    have impossible := closed parameter (.variable ⟨37⟩) (by simp)
    cases impossible

theorem same_raw_constructor {source : TypedSource} {admitted : ExpressionId → Prop}
    (ranges : ConstructorRanges source admitted) : ConstructorLaw source flexible admitted :=
  ConstructorLaw.of_ranges rfl ranges

/-- Empty substitution ranges do not justify rigid-binder well-formedness.
The selected-site consumer obtains that fact from actual source typing. -/
theorem empty_range_no_binders (parameter : TypeSystem.TypeParameterId) :
    let context : SourceSemantics.Context := {flexible with typeParameters := [parameter, parameter]}
    ParameterSubstitution.RangeAdmissible context [] ∧ ¬ TypeParameterBindersWellFormed context := by
  dsimp only
  refine ⟨?_, ?_⟩
  · intro other replacement member
    cases member
  · intro valid
    have unique := valid.1
    simp at unique
end Boundary

/-- Program signature identity is extracted from the same real source frame. -/
theorem actual_program_signatures : header.context.signatures = program.signatures :=
  header_program_signatures header

/-- This law is provided without any declaration range or validity callback.
It is scoped to successful selection and keeps the actual reached header. -/
theorem actual_selected_law {source : TypedSource} {context : SourceSemantics.Context}
    {admitted : ExpressionId → Prop} (same : context.signatures = program.signatures) :
    SelectedDeclarationLaw headers compilation source context admitted :=
  selected_validity same

private def content : String := String.intercalate "\n" [
  "enum Pair<A, B> { Pair(A, B) }",
  "function choose<A, B>(a: A, b: B) returns (A) { return a; }",
  "function side(x: Word) returns (Word) { return x; }",
  "function fail() returns (Word) { let written = 5; let gap: Word; return gap; }",
  "function unitRoot() { return choose((), 7); }",
  "function wordRoot() returns (Word) { return choose(side(7), side(7)); }",
  "function flagRoot() returns (Bool) { return choose(false, 13); }",
  "function dataRoot() returns (Pair<Word, Bool>) { return Pair(choose(17, false), true); }",
  "function lateFault() returns (Word) { return choose(side(19), fail()); }"
]
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue

private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) (names : List String) : IO Unit := do
  let prepared := compiled.indexed
  let diagnostics ← match prepared.base.diagnostics with
    | none => throw (IO.userError "selected expressions diagnostics missing")
    | some diagnostics => pure diagnostics.program
  let diagnostics := match prepared.base.callableContext with
    | none => diagnostics
    | some native => {diagnostics with rootTable := native.diagnostics.rootTable}
  let parents ← get "selected expressions parent contexts"
    (SourceCoreStageCodebook.prepareContexts prepared.base.sourceProgram prepared.base.plan
      (prepared.base.locals.bindings.flatMap (·.instances)))
  let mut calls := 0
  let mut generic := 0
  for named in prepared.base.functions do
    let original ← match prepared.base.sourceProgram.signatures.functions.find? (·.id == named.signature.key.declaration) with
      | some signature => pure signature | none => throw (IO.userError "selected expressions source signature missing")
    if names.contains original.name then
      let own ← match diagnostics.base.find? named.signature.key with
        | some own => pure own | none => throw (IO.userError "selected expressions own diagnostics missing")
      let source := CallableIndexedNamedGeneration.source named
      let compilation := CallableIndexedNamedGeneration.context prepared named
      let actual := (CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key []
      let scope := named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))
      let reasonAt := diagnostics.reasonAt named.signature.key
      let lower := SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram actual
        prepared.base.sourceProgram.signatures prepared.base.locals parents own.assignments diagnostics compilation
        prepared.base.callableContext none none
      let policy := {actual.expressions with callables := SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []}
      for item in source.nodes do
        match item with
        | .expression node => match node.form with
          | .call _ arguments (.declaration instantiation) =>
            let code ← get "selected expressions actual contextual output" (lower prepared.fuel source scope node.id reasonAt)
            let (slot, signature) ← get "selected expressions actual selection"
              (SourceCoreFunctions.selectedSignature policy compilation source node instantiation false)
            let reached ← match prepared.base.functions[slot]? with
              | some reached => pure reached | none => throw (IO.userError "selected expressions missing reached header")
            require (reached.signature == signature) "selected expressions full signature/slot mismatch"
            require (decide (instantiation = CallableNamedCanonicalOrder.retainedInstantiation reached.specialized))
              "selected expressions full retained source metadata mismatch"
            require (decide (instantiation.parameterSubstitution.map Prod.fst =
              (reached.specialized.parameterSubstitution.map Prod.fst).reverse))
              "selected expressions full domain order mismatch"
            let codes ← arguments.mapM (fun id => get "selected expressions ordered child" (lower (prepared.fuel - 1) source scope id reasonAt))
            require (code.expression == SourceCoreCalls.call signature
              (scope.length + compilation.administrativePrefix + slot) (SourceCoreCalls.packArguments codes).expression compilation.internalReason)
              "selected expressions actual call emission mismatch"
            calls := calls + 1
            if instantiation.parameterSubstitution.length == 2 then generic := generic + 1
          | _ => pure ()
        | _ => pure ()
  require (calls == 9 && generic == 5) s!"selected expressions coverage changed: calls={calls}, generic={generic}"

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name [] fuel initial
  pure (← get "selected expressions public resume" (first.resume 300000)).observation

private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (label : String) : IO Unit := do
  require (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap) s!"selected expressions old heap changed {label}"
  require (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"selected expressions ordered source cells changed {label}: {reprStr final.heap}"

def run : IO Unit := do
  let names := ["unitRoot", "wordRoot", "flagRoot", "dataRoot", "lateFault"]
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive named selected expressions" content names
  inspect compiled names
  let mut pair : Option DataConstructorInstantiation := none
  for named in compiled.indexed.base.functions do
    for item in (CallableIndexedNamedGeneration.source named).nodes do
      match item with
      | .expression node => match node.form with
        | .constructor instantiation _ => pair := some instantiation
        | _ => pure ()
      | _ => pure ()
  let actualPair ← match pair with
    | some instantiation => pure instantiation
    | none => throw (IO.userError "selected expressions constructor missing")
  let successes : List (String × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("unitRoot", .unit, [(.unit, some .unit), (.word, some (w 7))]),
    ("wordRoot", w 7, [(.word, some (w 7)), (.word, some (w 7)), (.word, some (w 7)), (.word, some (w 7))]),
    ("flagRoot", .bool false, [(.bool, some (.bool false)), (.word, some (w 13))]),
    ("dataRoot", .constructed actualPair [w 17, .bool true], [(.word, some (w 17)), (.bool, some (.bool false))])]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (w 819)⟩]}
  let baselines ← successes.mapM (fun test => finish compiled test.1 300000 initial)
  let failed ← finish compiled "lateFault" 300000 initial
  for fuel in [0, 43, 300000] do
    for (test, baseline) in successes.zip baselines do
      let (name, expected, expectedCells) := test
      let observed ← finish compiled name fuel initial
      require (reprStr observed == reprStr baseline) s!"selected expressions complete resume changed {name}"
      match observed with
      | .done actual final =>
        require (reprStr actual == reprStr expected) s!"selected expressions result changed {name}"
        cells initial final expectedCells name
      | _ => throw (IO.userError s!"selected expressions expected completion {name}")
    let observed ← finish compiled "lateFault" fuel initial
    require (reprStr observed == reprStr failed) "selected expressions fault resume changed"
    match observed with
    | .fault (.uninitializedLocal _) final =>
      cells initial final [(.word, some (w 19)), (.word, some (w 5)), (.word, none)] "lateFault"
    | _ => throw (IO.userError "selected expressions lost fault prefix")
  IO.println "recursive named selected expressions: actual selected header/full metadata/code, no named range callback, ordered cells/fault/resume GREEN"
end Tests.SourceCoreRecursiveNamedSelectedExpressions
