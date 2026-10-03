import Solcore.SourceSemantics.CoreLowering.RecursiveNamedResidualExpressionFactory
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Same-context instantiation closure is used by the real contextual compiler
and the unique body extractor. These tests keep full raw retained ranges;
execution checks are separate from the source/static proofs. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedResidualExpressions
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableAncestryPairedLookup
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open RecursiveNamedCatalogNativeContexts RecursiveNamedCatalogProfileFactory
open RecursiveGlobalInitializationMeaning RecursiveGlobalInitializationTyping
open RecursiveNamedExpressionCompilerCertificates RecursiveNamedCallSelectionCertificates
open CompatibleExpressionInstantiationLaws CompatibleSourceInstantiationClosure
open RecursiveNamedResidualExpressionFactory

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
    (declarationRanges : DeclarationRanges header.function.source expressionSyntax)
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
  exact RecursiveNamedResidualExpressionFactory.extract
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
    (declarationRanges := declarationRanges)
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
    (initialValid : CompatibleExpressionLiterals.ContextValid header.solved header.context header.function.evidence)
    (receipt : Receipt diagnosticPolicy headers header compilation expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))
    (interpreted : receipt.extracted.diagnostics registry faults) :
    Nonempty (ProfileFor diagnosticPolicy headers header compilation header.readFuel expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults) :=
  ⟨receipt.profile initialValid interpreted⟩

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

theorem same_raw_declaration {source : TypedSource} {admitted : ExpressionId → Prop}
    (ranges : DeclarationRanges source admitted) : DeclarationLaw source flexible admitted :=
  DeclarationLaw.of_ranges rfl ranges
end Boundary

private def content : String := String.intercalate "\n" [
  "enum Pair<A, B> { Pair(A, B) }",
  "function side(x: Word) returns (Word) { return x; }",
  "function truth(x: Bool) returns (Bool) { return x; }",
  "function choose<A, B>(a: A, b: B) returns (A) { return a; }",
  "function fail() returns (Word) { let written = 5; let gap: Word; return gap; }",
  "function rootWord() returns (Word) { return choose(side(7), truth(true)); }",
  "function rootBool() returns (Bool) { return choose(truth(false), side(9)); }",
  "function rootData() returns (Pair<Word, Bool>) { return Pair(side(11), truth(true)); }",
  "function nested() returns (Word) { return choose(choose(side(3), truth(true)), side(5)); }",
  "function paired() returns ((Word, Bool)) { return (choose(side(13), truth(true)), truth(false)); }",
  "function indexed(m: mapping(Bool => Word)) returns (Word) { return m[choose(truth(true), side(17))]; }",
  "function firstFault() returns (Word) { return choose(fail(), side(99)); }",
  "function laterFault() returns (Word) { return choose(side(19), fail()); }"
]
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue

/-- Re-enter the actual compiler callback using the real named source, global
inventory and parameter scope. These checks do not synthesize static source
judgments or treat runtime observation as evidence for a formal Tree. -/
private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) (names : List String) : IO Unit := do
  let prepared := compiled.indexed
  let diagnostics ← match prepared.base.diagnostics with
    | none => throw (IO.userError "residual expressions diagnostics missing")
    | some diagnostics => pure diagnostics.program
  let diagnostics := match prepared.base.callableContext with
    | none => diagnostics
    | some native => {diagnostics with rootTable := native.diagnostics.rootTable}
  let parents ← get "residual expressions parent contexts"
    (SourceCoreStageCodebook.prepareContexts prepared.base.sourceProgram prepared.base.plan
      (prepared.base.locals.bindings.flatMap (·.instances)))
  let mut callCount := 0
  let mut genericCount := 0
  let mut formCount := 0
  let mut constructorCount := 0
  for named in prepared.base.functions do
    let original ← match prepared.base.sourceProgram.signatures.functions.find? (·.id == named.signature.key.declaration) with
      | some signature => pure signature | none => throw (IO.userError "residual expressions source signature missing")
    if names.contains original.name then
      let own ← match diagnostics.base.find? named.signature.key with
        | some own => pure own | none => throw (IO.userError "residual expressions own diagnostics missing")
      let source := CallableIndexedNamedGeneration.source named
      let compilation := CallableIndexedNamedGeneration.context prepared named
      let actual := (CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key []
      let scope := named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))
      let reasonAt := diagnostics.reasonAt named.signature.key
      let lower := SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram actual
        prepared.base.sourceProgram.signatures prepared.base.locals parents own.assignments diagnostics compilation
        prepared.base.callableContext none none
      for item in source.nodes do
        match item with
        | .expression node =>
          match node.form with
          | .reference _ (.declaration _) => pure ()
          | _ =>
            let code ← get "actual contextual expression" (lower prepared.fuel source scope node.id reasonAt)
            let nativeContext := SourceCoreLocalCell.coreContext scope ++ named.signature.parameterType ::
              prepared.base.globals.map (·.referenceType) ++ [.cell prepared.ancestry.layout.frame.type]
            require (Core.infer? nativeContext code.expression prepared.layouts.definitions == some (LanguageResult.resultType code.type))
              "actual contextual expression lost native type"
            formCount := formCount + 1
            match node.form with
            | .call _ arguments (.declaration instantiation) =>
              let key ← get "actual static instantiation target" (SourceCompilationPlan.exactInstantiationKey compilation.plan instantiation)
              let specialized ← get "actual full static record" (SourceCompilationPlan.exactSpecialization compilation.plan key)
              require (decide (instantiation = CallableNamedCanonicalOrder.retainedInstantiation specialized))
                "residual expressions changed complete retained instantiation"
              require (decide (instantiation.parameterSubstitution.map Prod.fst = (specialized.parameterSubstitution.map Prod.fst).reverse))
                "residual expressions changed retained domain order"
              require (instantiation.parameterSubstitution.all (fun row => SourceCoreDataCatalog.closed row.2))
                "residual expressions retained open named substitution"
              let rows := compilation.globals.zipIdx.filter (fun row => decide (row.1.key = key))
              let (signature, index) ← match rows with
                | [row] => pure row | _ => throw (IO.userError "residual expressions actual full global row missing")
              require (compiled.indexed.base.functions[index]?.map (·.signature) == some signature)
                "residual expressions header slot does not contain complete signature"
              let codes ← arguments.mapM (fun id => get "ordered actual child code" (lower (prepared.fuel - 1) source scope id reasonAt))
              require (codes.length == arguments.length && arguments.length == specialized.function.typedBody.inputs.length)
                "residual expressions actual argument arity/order lost"
              require (code.expression == SourceCoreCalls.call signature
                (scope.length + compilation.administrativePrefix + index) (SourceCoreCalls.packArguments codes).expression compilation.internalReason)
                "residual expressions ordered argument emission changed"
              callCount := callCount + 1
              if specialized.parameterSubstitution.length == 2 then genericCount := genericCount + 1
            | .constructor instantiation _ =>
              constructorCount := constructorCount + 1
              require (instantiation.parameterSubstitution.length == 2 &&
                instantiation.parameterSubstitution.all (fun row => SourceCoreDataCatalog.closed row.2))
                "residual expressions lost full closed constructor range"
            | _ => pure ()
        | _ => pure ()
  require (callCount == 26 && genericCount == 8 && formCount == 46 && constructorCount == 1)
    s!"residual expressions fixture coverage changed: calls={callCount}, generic={genericCount}, nodes={formCount}, constructors={constructorCount}"

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← get "residual expressions public resume" (first.resume 300000)).observation
private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (label : String) : IO Unit := do
  require (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap) s!"residual expressions old heap changed {label}"
  require (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"residual expressions ordered source cells changed {label}: {reprStr final.heap}"

def run : IO Unit := do
  let names := ["rootWord", "rootBool", "rootData", "nested", "paired", "indexed", "firstFault", "laterFault"]
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive named residual expressions" content names
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
    | none => throw (IO.userError "residual expressions generic constructor missing")
  let mapping : SourceTypedRuntime.Value := .mapping .bool .word [(.bool true, w 31), (.bool true, w 91)]
  let successes : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("rootWord", [], w 7, [(.word, some (w 7)), (.bool, some (.bool true)), (.word, some (w 7)), (.bool, some (.bool true))]),
    ("rootBool", [], .bool false, [(.bool, some (.bool false)), (.word, some (w 9)), (.bool, some (.bool false)), (.word, some (w 9))]),
    ("rootData", [], .constructed actualPair [w 11, .bool true], [(.word, some (w 11)), (.bool, some (.bool true))]),
    ("nested", [], w 3, [(.word, some (w 3)), (.bool, some (.bool true)), (.word, some (w 3)), (.bool, some (.bool true)),
      (.word, some (w 5)), (.word, some (w 3)), (.word, some (w 5))]),
    ("paired", [], .product (w 13) (.bool false), [(.word, some (w 13)), (.bool, some (.bool true)),
      (.word, some (w 13)), (.bool, some (.bool true)), (.bool, some (.bool false))]),
    ("indexed", [mapping], w 31, [(.mapping .bool .word, some mapping), (.bool, some (.bool true)),
      (.word, some (w 17)), (.bool, some (.bool true)), (.word, some (w 17))])]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (w 819)⟩]}
  let baselines ← successes.mapM (fun test => finish compiled test.1 test.2.1 300000 initial)
  let failed ← ["firstFault", "laterFault"].mapM (fun name => finish compiled name [] 300000 initial)
  for fuel in [0, 43, 300000] do
    for (test, baseline) in successes.zip baselines do
      let (name, arguments, expected, expectedCells) := test
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) s!"residual expressions complete resume changed {name}"
      match observed with
      | .done actual final =>
        require (reprStr actual == reprStr expected) s!"residual expressions result changed {name}"
        cells initial final expectedCells name
      | _ => throw (IO.userError s!"residual expressions expected completion {name}")
    for (name, baseline) in ["firstFault", "laterFault"].zip failed do
      let observed ← finish compiled name [] fuel initial
      require (reprStr observed == reprStr baseline) s!"residual expressions fault resume changed {name}"
      match observed with
      | .fault (.uninitializedLocal _) final =>
        let earlier := if name == "laterFault" then [(.word, some (w 19))] else []
        cells initial final (earlier ++ [(.word, some (w 5)), (.word, none)]) name
      | _ => throw (IO.userError "residual expressions lost ordered source fault")
  IO.println "recursive named residual expressions: actual contextual output, full closed raw ranges, same-header extraction, ordered heap/fault/resume GREEN"
end Tests.SourceCoreRecursiveNamedResidualExpressions
