import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedStageContracts
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Public factory consumers use the same cached artifact and codebook.
Guard rejection keeps the original callee store and never requires argument
or callable-body execution. Source callable provenance remains explicit. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedPreparedStageContracts
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open RecursiveNamedPreparedStageContracts

abbrev actual_public_pipeline := @public_compilation
abbrev actual_public_stage_table := @of_public_compile
abbrev actual_indirect_emission := @indirect_call_eq
abbrev actual_ordered_rows := @Prepared.rows
abbrev actual_dispatch_coverage := @Prepared.covers

/-- Actual rows construct the dispatch from source provenance. The only native
child premise is the original callee evaluation; arguments are never replayed. -/
theorem original_callee_stage_failure
    {compiled : SourceCoreUnifiedCompilation.Compiled} {native : SourceCoreGeneralFunctions.CallableContext}
    (prepared : Prepared compiled native) {context : SourceCoreFunctions.Context}
    {site : SourceCoreCallableContracts.Callsite} {sidecar : SourceCoreStageContracts.Sidecar}
    {node : ExpressionNode} {callee : ExpressionId} {arguments : List ExpressionId}
    {metadata : IndirectCallResolution}
    (issued : SourceCoreCallableContracts.prepareCallsite native.table context.owner node.id
      native.diagnostics.reasonAt = .ok site)
    (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan context.owner = .ok sidecar)
    (contains : ContainsExpression sidecar.source node.id node)
    (form : node.form = .call callee arguments (.indirect metadata))
    {sourceValue : Dynamic.Value} {carrier : Core.Value} {contract : Staging.CallGuard.Contract}
    (origin : CallableLedger.OriginRep sidecar.plan site.table sourceValue carrier)
    (bound : (CallableLedger.frame sidecar).Binds sourceValue contract)
    {reason : Staging.CallGuard.Fault}
    (rejected : Staging.CallBoundary.GuardRejects (CallableLedger.frame sidecar) node.id arguments sourceValue reason)
    {environment : Environment} {before after : Store} {calleeCode : Expr}
    (evaluated : Evaluates environment before calleeCode (.inRight .word carrier) after)
    (result : Core.Ty) (argumentsCode : Expr) :
    ∃ token,
      Evaluates environment before (site.lower native.diagnostics.unknown result calleeCode argumentsCode)
        (.inLeft result (.word token)) after ∧ CallStageBoundary.ReasonRepresents site reason token := by
  obtain ⟨dispatch⟩ := CallableLedger.dispatch (prepared.rows issued caller contains form) origin bound
  have actual := evaluated
  rw [dispatch.shape] at actual
  exact ⟨dispatch.reason reason,
    site.lower_stage_failure native.diagnostics.unknown dispatch.row _ dispatch.found (dispatch.rejected rejected) actual,
    dispatch.reason_represents reason⟩

/-- Verdict reflection uses the independent guard judgment and needs neither
source execution nor a preservation result. -/
theorem guard_acceptance (guard : SourceCoreStageContracts.Guard) :
    guard.decision = .ok () ↔
      Staging.CallGuard.Accepts (CallStageGuard.frame guard.sidecar.caller)
        ⟨guard.contract.parameters, guard.contract.stagedResult⟩ guard.node.id guard.arguments :=
  CallStageGuard.guard_accepts_iff guard

theorem absent_context {compiled : SourceCoreUnifiedCompilation.Compiled}
    (absent : compiled.indexed.base.callableContext = none)
    (native : SourceCoreGeneralFunctions.CallableContext) : ¬ Prepared compiled native := by
  intro prepared
  have present := prepared.present
  rw [absent] at present
  cases present

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def w := Word.ofNatModulo
private def content : String := String.intercalate "\n" [
  "function marked(comptime item: Word) returns (Word) { return item; }",
  "function identity(item: Word) returns (Word) { return item; }",
  "function namedFault(value: Word) returns (Word) { let f = marked; return f(value); }",
  "function lambdaFault(value: Word) returns (Word) { let f = lam(comptime item: Word) -> Word { return item; }; return f(value); }",
  "function ordinary(value: Word) returns (Word) { let f = identity; return f(value); }",
  "function tupleParameter() returns (Word) { let f = lam(value: (Word, Word)) -> Word { return 7; }; return f(1, 2); }",
  "function effectfulTuple() returns (comptime<Word>) { let f = lam(value: (Word, Word)) -> Word { return 7; }; return f(1, 2); }",
  "function builtin(value: Word) returns (integer) { let op = wordToInteger; return op(value); }"
]

private def contractFields (contract : SourceCoreStageContracts.Contract) :=
  (contract.plan, contract.parameters, contract.stagedResult, contract.owner)

private def rowFields (row : SourceCoreStageCodebook.Decision) :=
  (row.caller, row.call, row.entry.id, row.entry.origin, row.entry.parameterCount,
    row.entry.contract.map contractFields, row.argumentCount,
    row.guard.map fun guard => (guard.sidecar.plan, guard.sidecar.caller, guard.node,
      guard.arguments, contractFields guard.contract, guard.decision))

/-- Every guard row belongs to the artifact compiled through the public path.
The low-level rejection probe uses its real descriptor ID; no source origin is
inferred for the explicit probe carrier. -/
private def audit (cached : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let native ← match cached.indexed.base.callableContext with
    | some native => pure native | none => throw (IO.userError "actual stage context missing")
  let table := native.table
  require (!table.entries.isEmpty && !table.decisions.isEmpty) "actual codebook inventory empty"
  let mut rejected := 0
  let mut accepted := 0
  let mut effectful := 0
  for row in table.decisions do
    let site ← get "actual prepared callsite"
      (SourceCoreCallableContracts.prepareCallsite table row.caller row.call native.diagnostics.reasonAt)
    let selected ← match site.rowAt? row.entry.id with
      | some selected => pure selected | none => throw (IO.userError "actual ordered row lookup missing")
    require (reprStr (rowFields selected) == reprStr (rowFields row)) "actual callsite changed its complete row"
    match row.guard with
    | none =>
      require row.entry.contract.isNone "user callable lost its guard"
      require row.beforeArguments.toOption.isSome "builtin acquired a before-arguments guard"
    | some guard =>
      require (guard.node.id == row.call && guard.sidecar.caller.key == row.caller &&
        guard.arguments.length == row.argumentCount) "actual source caller/argument identity changed"
      require (reprStr guard.decision == reprStr
        (SourceCompilationPlan.validateStagedCallableContract guard.sidecar.caller guard.node guard.arguments
          guard.contract.parameters guard.contract.stagedResult guard.contract.owner))
        "actual guard validator equation changed"
      if guard.sidecar.caller.function.returnComptime then
        effectful := effectful + 1
        require row.beforeArguments.toOption.isSome "effectful caller acquired an early stage guard"
      match row.beforeArguments with
      | .ok () => accepted := accepted + 1
      | .error error =>
        rejected := rejected + 1
        let token := site.reasonAt row.caller row.call row.entry.id .beforeArguments error
        let carrier : Core.Value := .pair (.closure .unit .unit .unit []) (.word row.entry.id)
        let initialStore : Store := [.closure .unit .unit .unit [], .word (w 0)]
        let environment : Environment := [.cellRef .word 1, carrier]
        let calleeCode : Expr := .letE (.storeCell (.var 0) (.word (w 11))) (LanguageResult.success (.var 2))
        let argumentsCode : Expr := .letE (.storeCell (.var 0) (.word (w 22))) (LanguageResult.success .unit)
        let code := site.lower native.diagnostics.unknown .unit calleeCode argumentsCode
        for fuel in [0, 1, 31, 30000] do
          let first := runStateful fuel (.initial code environment initialStore)
          let final := match first with
            | .outOfFuel state => runStateful 30000 state
            | other => other
          require (final == .done (.inLeft .unit (.word token))
            [.closure .unit .unit .unit [], .word (w 11)])
            "stage rejection ran arguments, changed the original prefix or lost the callee store"
  require (rejected > 0 && accepted > 0 && effectful > 0) "actual guard branch coverage incomplete"
  for function in BuiltinFunctionId.all do
    let id ← match table.idAt? (.builtin function) with
      | some id => pure id | none => throw (IO.userError "actual builtin descriptor missing")
    let entry ← match table.entryAt? id with
      | some entry => pure entry | none => throw (IO.userError "actual builtin row missing")
    require (entry.parameterCount == function.parameterTypes.length && entry.contract.isNone)
      "actual builtin contract or ordered arity changed"

def run : IO Unit := do
  let program ← get "stage actual checked program" (checkProgram {
    entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content}] })
  let names := ["namedFault", "lambdaFault", "ordinary", "tupleParameter", "effectfulTuple", "builtin"]
  let roots ← names.mapM (SourceCoreUnifiedCorpusSupport.key program)
  let seeds := roots.map fun key => SourceCoreCompiler.Seed.declaration key.declaration
  let options : SourceCompiler.Options := {specializationBudget := 512, compilationFuel := 1000}
  let facade ← get "actual public stage compilation" (SourceCompiler.compileChecked program seeds options)
  let source ← get "actual same Core compiler" (SourceCoreCompiler.compileChecked program seeds options)
  let cached ← match source.artifact? with
    | some cached => pure cached | none => throw (IO.userError "nonempty stage roots lost the cache")
  require (facade.keys == source.keys && cached.keys == roots) "public stage root order changed"
  let recipe ← get "actual stage recipe" (SourceCoreIndexedSession.Recipe.prepare cached)
  audit recipe.compiled
  let empty ← get "actual public empty roots" (SourceCoreCompiler.compileChecked program [] options)
  require empty.artifact?.isNone "empty root path invented a codebook"
  let artifact ← recipe.open
  let boot ← artifact.bootstrapFresh
  let initial ← match boot.resume 300000 with
    | .ready session => pure session
    | _ => throw (IO.userError "actual stage bootstrap did not finish")
  for fuel in [0, 1, 31, 300000] do
    let checkpoint ← get "actual ordinary guarded startup"
      (initial.start (← SourceCoreUnifiedCorpusSupport.key program "ordinary") [.word (w 17)])
    let first ← checkpoint.resume fuel
    let final ← match first with
      | .outOfFuel checkpoint => checkpoint.resume 300000
      | other => pure other
    match final with
    | .succeeded completion =>
      require (completion.value == .word (w 17) && completion.session.installedGlobalsPresent)
        "actual ordinary guarded result/global prefix changed"
    | _ => throw (IO.userError "actual ordinary guarded call did not succeed")
  IO.println "actual public compiled stage table / original ordered guards / builtin and effectful bypass / callee-only fault store / full prefix and resume GREEN"

end Tests.SourceCoreRecursiveNamedPreparedStageContracts
