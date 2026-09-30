import Solcore.Frontend.SourceCoreStageCodebook

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
