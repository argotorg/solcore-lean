import Solcore.Frontend.SourceCoreCallableViews
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCallableViews.Principal.mk
#check_failure Solcore.Frontend.SourceCoreCallableViews.View.mk
#check_failure Solcore.Frontend.SourceCoreCallableViews.Table.mk
#check_failure Solcore.Frontend.SourceCoreCallableViews.Entry.mk

/-! Actual compatible artifacts retain occurrence-specific local wrapper
metadata, including empty monomorphic views, distinct qualified witnesses and
nested cumulative contexts. This is static inventory, not closure export. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableViews
open Solcore Solcore.Frontend SourceInference TypeSystem
open SourceCoreCallableViews
abbrev Prepared := SourceCoreCompatibleFunctions.Prepared

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}", "impl Mark<Bool> {}",
    "type WordFunction = function(Word) returns (Word);",
    "function keep<T>(item: T) returns (T) where T: Mark { return item; }",
    "function mono() returns (WordFunction) { let f: WordFunction = lam(item: Word) -> Word { return item; }; return f; }",
    "function repeated(flag: Bool) returns (Word, Word, Bool) {",
    " let f = lam(item) { return keep(item); }; return (f(1), f(2), f(flag)); }",
    "function nested(flag: Bool) returns (Word, Word) {",
    " let outer = lam(value) { keep(value); let inner = lam(item) { return keep(item); }; return inner(1); };",
    " return (outer(1), outer(flag)); }",
    "function nestedMono(flag: Bool) returns (Word, Word) {",
    " let outer = lam(value) { keep(value); let f: WordFunction = lam(item: Word) -> Word { return item; }; return f(1); };",
    " return (outer(1), outer(flag)); }"
  ]}] }

private def key (program : CheckedProgram) (name : String) : IO Key := do
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError s!"callable views fixture missing: {name}")

private def artifact (program : CheckedProgram) (name : String) : IO SourceCoreCompatibleFunctions.Automatic := do
  let owner ← key program name
  let plan ← match SourceSpecializationWorklist.run program [⟨owner.declaration, []⟩] 128 with
    | .ok (.complete plan) => pure plan
    | other => throw (IO.userError s!"callable views worklist failed: {reprStr other}")
  match SourceCoreCompatibleFunctions.prepare program plan 256 with
  | .ok artifact => pure artifact
  | .error error => throw (IO.userError s!"callable views compatible artifact failed: {reprStr error}")

example {program : CheckedProgram} {plan : Plan} (view : View program plan) :
    view.cumulative = view.ownSubstitution.compose view.parentActive := view.cumulativeExact

example {program : CheckedProgram} {plan : Plan} (view : View program plan) :
    view.reference.witnesses = view.ownWitnesses := view.witnessesExact

example {program : CheckedProgram} {plan : Plan} (view : View program plan) :
    SourceCoreLocalEvidence.authenticateReference program plan
      { caller := view.principal.owner, source := view.principal.originalSource,
        binder := view.principal.binder, initializer := view.principal.initializer, instances := [] }
      view.parent view.read = .ok view.reference := view.authenticatedReference

example {program : CheckedProgram} {plan : Plan} (view : View program plan) :
    view.principal.source = SourceTypedRuntime.rewriteLocalRequirements view.inheritedWitnesses
      (view.principal.originalSource.applySubstitution view.parentActive) := view.exactPrincipalSource

example {program : CheckedProgram} {plan : Plan} (view : View program plan) :
    ∃ node, view.principal.source.lookupExpression? view.principal.initializer = some node ∧
      node.form = .lambda view.principal.parameters view.principal.resultType view.principal.body :=
  view.principal.lambdaMetadata

example {program : CheckedProgram} {plan : Plan} (view : View program plan) :
    SourceCompilationPlan.localRequirementWitnesses view.compilerCaller view.principal.evidence
      (view.principal.binder.applySubstitution view.parentActive) view.rawRead =
      .ok (view.ownSubstitution, view.ownWitnesses) := view.exactFactory

private def table {checked : Checked} (prepared : Prepared checked) : IO (Table prepared.sourceProgram prepared.plan) :=
  match prepare prepared with
  | .ok result => pure result
  | .error error => throw (IO.userError s!"callable views inventory rejected: {reprStr error}")

private def checks {checked : Checked} (prepared : Prepared checked) (table : Table prepared.sourceProgram prepared.plan) : IO Unit := do
  assertTrue (!table.entries.isEmpty) "callable view inventory unexpectedly empty"
  for entry in table.entries do
    let view := entry.view
    assertTrue (view.read.occurrence.owner == view.owner.declaration && view.principal.source.owner == view.owner.declaration)
      "callable view lost actual occurrence ownership"
    assertTrue (view.principal.source == SourceTypedRuntime.rewriteLocalRequirements view.inheritedWitnesses
      (view.principal.originalSource.applySubstitution view.parentActive)) "principal source used the compiler ledger instead of the runtime source metadata"
    assertTrue (view.compilerCaller.function.typedBody == view.principal.originalSource.applySubstitution view.parentActive)
      "compiler caller used occurrence wrapper substitution as parent context"
    assertTrue (view.wrapsPrincipal == !view.binding.binder.scheme.quantified.isEmpty)
      "monomorphic/generated wrapper decision changed"
    assertTrue ((table.viewAt? view.owner view.read view.parentActive).map (·.id) == some entry.id &&
      (table.entryAt? entry.id).map (·.id) == some entry.id) "callable view lookup/id changed"
    assertTrue (view.reference.witnesses.length == view.ownWitnesses.length)
      "view lost own occurrence witnesses"
    if view.wrapsPrincipal then
      let selected ← match view.selectedInstance with
        | some selected => pure selected | none => throw (IO.userError "wrapped read has no actual compiled local candidate")
      assertTrue (selected.origin.substitution == view.cumulative && selected.origin.initializer == view.principal.initializer)
        "read selected a candidate by final type rather than full cumulative context"
    else
      assertTrue (view.ownSubstitution.isEmpty && view.ownWitnesses.isEmpty && view.selectedInstance.isNone)
        "monomorphic principal unexpectedly acquired wrapper metadata"
  match prepare prepared {} 0 with
  | .error .zeroFirstId => pure () | _ => throw (IO.userError "zero callable view ID accepted")
  match prepare prepared {} (2 ^ 256) with
  | .error (.idSpaceExhausted _) => pure () | _ => throw (IO.userError "callable view Word ID wrapped")
  match prepare prepared {maxViews := 0} with
  | .error (.viewBudgetExhausted 0) => pure () | _ => throw (IO.userError "callable view count budget ignored")
  match prepare prepared {maxSourceNodes := 0} with
  | .error (.sourceNodeBudgetExhausted 0) => pure () | _ => throw (IO.userError "callable view source inventory budget ignored")

private def checkAuthenticationErrors {checked : Checked} (prepared : Prepared checked)
    (table : Table prepared.sourceProgram prepared.plan) : IO Unit := do
  let view ← match table.entries.head? with
    | some entry => pure entry.view | none => throw (IO.userError "callable view tamper fixture empty")
  let other ← key prepared.sourceProgram "keep"
  let foreign := {view.read with occurrence := {view.read.occurrence with owner := other.declaration}}
  match authenticate prepared.sourceProgram prepared.plan view.binding view.parent foreign with
  | .error _ => pure () | .ok _ => throw (IO.userError "foreign occurrence accepted as local view")
  let altered := {view.binding with initializer := foreign}
  match authenticate prepared.sourceProgram prepared.plan altered view.parent view.read with
  | .error (.evidence (.bindingMismatch _)) => pure ()
  | _ => throw (IO.userError "altered principal initializer accepted")
  let duplicateSource := {view.binding.source with nodes := view.binding.source.nodes ++ view.binding.source.nodes}
  let duplicate := {view.binding with source := duplicateSource}
  match authenticate prepared.sourceProgram prepared.plan duplicate view.parent view.read with
  | .error (.evidence (.originMismatch _)) => pure ()
  | _ => throw (IO.userError "duplicate foreign source table accepted")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program | .error error => throw (IO.userError s!"callable views source rejected: {reprStr error}")
  let mono ← artifact program "mono"
  let monoTable ← table mono.prepared
  checks mono.prepared monoTable
  checkAuthenticationErrors mono.prepared monoTable
  assertTrue (monoTable.entries.length == 1 && monoTable.entries.all (fun entry => !entry.view.wrapsPrincipal))
    "monomorphic direct lambda metadata missing or wrapped"
  let repeated ← artifact program "repeated"
  let repeatedTable ← table repeated.prepared
  checks repeated.prepared repeatedTable
  let f := repeatedTable.entries.filter (fun entry => entry.view.binding.binder.name == "f")
  assertTrue (f.length == 3 && f.all (fun entry => entry.view.parentActive.isEmpty && entry.view.ownWitnesses.length == 1))
    "same-type repeated reads lost occurrence-specific witnesses"
  let actualRequirements := f.flatMap (fun entry => entry.view.ownWitnesses.map (·.actualRequirement))
  assertTrue (actualRequirements.eraseDups.length == 3) "qualified read requirements merged by principal/type"
  let nested ← artifact program "nested"
  let nestedTable ← table nested.prepared
  match prepare nested.prepared {maxContexts := 0} with
  | .error (.contextBudgetExhausted 0) => pure ()
  | _ => throw (IO.userError "local context inventory budget ignored")
  checks nested.prepared nestedTable
  let inner := nestedTable.entries.filter (fun entry => entry.view.binding.binder.name == "inner")
  assertTrue (inner.length == 2 && inner.all (fun entry => !entry.view.parentActive.isEmpty &&
    !entry.view.ownSubstitution.isEmpty && entry.view.cumulative != entry.view.ownSubstitution))
    "nested parent active context collapsed into own wrapper substitution"
  assertTrue ((inner.map (fun entry => entry.view.parentActive)).eraseDups.length == 2)
    "equal inner result types erased distinct enclosing contexts"
  let nestedMono ← artifact program "nestedMono"
  let nestedMonoTable ← table nestedMono.prepared
  checks nestedMono.prepared nestedMonoTable
  let nestedF := nestedMonoTable.entries.filter (fun entry => entry.view.binding.binder.name == "f")
  assertTrue (nestedF.length == 2 && nestedF.all (fun entry => !entry.view.wrapsPrincipal &&
    !entry.view.parentActive.isEmpty && entry.view.ownSubstitution.isEmpty)) "nested monomorphic closure lost parent metadata"
  IO.println "static callable views, exact witnesses/principal sources, mono/nested context and rejection GREEN"
end Tests.SourceCoreCallableViews
