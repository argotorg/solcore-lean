import Solcore.Frontend.SourceCoreLocalEvidence

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreLocalEvidence.Prepared.mk
#check_failure Solcore.Frontend.SourceCoreLocalEvidence.Reference.mk
#check_failure fun (prepared : Solcore.Frontend.SourceCoreLocalEvidence.Prepared) => { prepared with witnesses := [] }
#check_failure fun (reference : Solcore.Frontend.SourceCoreLocalEvidence.Reference) => { reference with owned := [] }

/-! Qualified template assumptions remain at their original body requirement
IDs after contextual authentication. These are static compiler receipts; the
public compiler's executable routing is tested by its owning module. -/

set_option autoImplicit false

namespace Tests.SourceCoreLocalEvidence

open Solcore Solcore.Frontend SourceInference TypeSystem SourceCoreLocalEvidence
abbrev Catalog := SourceCoreLocalPolymorphism.Catalog

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}", "impl Mark<Bool> {}",
    "trait Coerce<From, To> { function coerce(value: From) returns (To); }",
    "type WordFunction = function(Word) returns (Word);",
    "impl Coerce<WordFunction, Word> { function coerce(value: WordFunction) returns (Word) { return value(5); } }",
    "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
    "function qualified(flag: Bool) returns (Word, Bool) {",
    " let f = lam(item) { return keep(item); }; return (f(1), f(flag)); }",
    "function coerced() returns (Word) { let f: WordFunction = lam(item: Word) -> Word { return keep(item); }; return f; }",
    "function nested(flag: Bool) returns (Word, Word) {",
    " let outer = lam(value) { keep(value);",
    "   let inner = lam(item) { return keep(item); }; return inner(1); };",
    " return (outer(1), outer(flag)); }"
  ] }] }

private def plan (program : CheckedProgram) (name : String) : IO SourceSpecializationWorklist.Plan := do
  let signature ← match program.signatures.functions.filter (·.name == name) with
    | [signature] => pure signature
    | _ => throw (IO.userError s!"local evidence fixture missing: {name}")
  match SourceSpecializationWorklist.run program [⟨signature.id, []⟩] 64 with
  | .ok (.complete plan) => pure plan
  | other => throw (IO.userError s!"local evidence worklist failed: {reprStr other}")

private def catalog (checked : SourceCoreDataCatalog.Checked) (plan : SourceSpecializationWorklist.Plan) : IO Catalog :=
  match SourceCoreLocalPolymorphism.prepare checked plan with
  | .ok catalog => pure catalog
  | .error error => throw (IO.userError s!"local evidence catalog failed: {reprStr error}")

private def binding (catalog : Catalog) (name : String) : IO Binding :=
  match catalog.bindings.filter (·.binder.name == name) with
  | [binding] => pure binding
  | _ => throw (IO.userError s!"local evidence binding missing: {name}")

private def prepared (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (candidate : Instance) (parent : Option Prepared := none) : IO Prepared :=
  match prepare program plan candidate parent with
  | .ok prepared => pure prepared
  | .error error => throw (IO.userError s!"local evidence receipt failed: {reprStr error}")

private def checkCalls (prepared : Prepared) : IO Unit := do
  let calls := prepared.source.nodes.filterMap fun
    | .expression node@{ form := .call _ _ (.declaration instantiation), .. } =>
        if instantiation.predicates.all (fun predicate => (TypedTraitResolution.predicateVariables predicate).isEmpty) then
          some (node, instantiation)
        else none
    | _ => none
  for (node, instantiation) in calls do
    match SourceCompilationPlan.exactDirectCallRuntimeEvidence prepared.caller node [] instantiation with
    | .ok evidence =>
        assertTrue (evidence.length == instantiation.predicates.length)
          "contextual direct-call evidence lost a source obligation"
    | .error error => throw (IO.userError s!"contextual call ledger rejected: {reprStr error}")

example (substitution : Substitution) (witnesses : List Witness) (rows : List SolvedRequirement) :
    (rewriteLedger substitution witnesses rows).map (·.id) = rows.map (·.id) :=
  rewriteLedger_ids substitution witnesses rows

example (reference : Reference) : reference.normalized.coercions = reference.original.coercions :=
  reference.normalized_coercions

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"local evidence source failed: {reprStr error}")
  let checked ← match SourceCoreDataCatalog.prepare program.signatures 128 [.word, .bool] with
    | .ok checked => pure checked
    | .error error => throw (IO.userError s!"local evidence catalog failed: {reprStr error}")
  let qualifiedPlan ← plan program "qualified"
  let qualifiedCatalog ← catalog checked qualifiedPlan
  let f ← binding qualifiedCatalog "f"
  assertTrue (f.instances.length == 2 && f.binder.schemeRequirements.length == 1)
    "qualified fixture lost Word/Bool instances or its template"
  for candidate in f.instances do
    let child ← prepared program qualifiedPlan candidate
    assertTrue (child.caller.key == candidate.origin.caller && child.substitution == candidate.origin.substitution &&
      child.caller.function.type == (qualifiedPlan.specializations.find? (·.key == candidate.origin.caller) |>.map
        (·.function.type) |>.getD .error)) "qualified child changed its global signature or contextual key"
    assertTrue (child.caller.function.solvedRequirements.map (·.id) == candidate.origin.solvedRequirements.map (·.id))
      "qualified child erased or re-numbered a body requirement"
    assertTrue (child.witnesses.length == 1) "qualified child failed to discharge one template assumption"
    for witness in child.witnesses do
      let row ← match child.caller.function.solvedRequirements.filter (·.id == witness.templateRequirement) with
        | [row] => pure row
        | _ => throw (IO.userError "qualified template row disappeared")
      match row.evidence with
      | .implementation evidence =>
          assertTrue (evidence == witness.evidence && row.predicate == witness.predicate)
            "qualified child substituted an unauthenticated implementation"
      | _ => throw (IO.userError "qualified template assumption remained unresolved")
    checkCalls child
  let readIds := f.source.nodes.filterMap fun
    | .expression { id, form := .reference _ (.local binder), .. } => if binder == f.binder.id then some id else none
    | _ => none
  for id in readIds do
    match authenticateReference program qualifiedPlan f none id with
    | .ok reference =>
        assertTrue (!reference.original.requirements.isEmpty && reference.normalized.requirements.isEmpty)
          "qualified reference silently dropped an unbound obligation or kept its bound scheme obligation"
        assertTrue (reference.normalized.form == reference.original.form &&
          reference.normalized.coercions == reference.original.coercions &&
          reference.normalized.span == reference.original.span &&
          reference.normalized.type == reference.original.type) "reference normalization changed source metadata"
        match normalizeOccurrence program qualifiedPlan f none f.source id with
        | .ok source =>
            assertTrue (source.lookupExpression? id == some reference.normalized)
              "policy metadata traversal did not remove its authenticated qualified requirement"
        | .error error => throw (IO.userError s!"qualified policy metadata normalization failed: {reprStr error}")
    | .error error => throw (IO.userError s!"qualified local read authentication failed: {reprStr error}")

  let coercedPlan ← plan program "coerced"
  let coercedF ← match coercedPlan.specializations.find? (·.function.typedBody.nodes.any fun
      | .statement { form := .letDecl binder _, .. } => binder.name == "f"
      | _ => false) with
    | none => throw (IO.userError "coerced local caller disappeared")
    | some caller =>
        match caller.function.typedBody.nodes.findSome? fun
          | .statement { form := .letDecl binder (some initializer), .. } =>
              if binder.name == "f" then some (binder, initializer) else none
          | _ => none with
        | none => throw (IO.userError "coerced local binder disappeared")
        | some (binder, initializer) => pure ({
            caller := caller.key
            source := caller.function.typedBody
            binder
            initializer
            instances := [] } : Binding)
  let coercedId ← match coercedF.source.nodes.findSome? fun
      | .expression node@{ form := .reference _ (.local binder), .. } =>
          if binder == coercedF.binder.id then some node.id else none
      | _ => none with
    | some id => pure id
    | none => throw (IO.userError "coerced local reference disappeared")
  let receipt ← match authenticateReference program coercedPlan coercedF none coercedId with
    | .ok receipt => pure receipt
    | .error error => throw (IO.userError s!"coerced local authentication failed: {reprStr error}")
  assertTrue (!receipt.original.coercions.isEmpty && !receipt.normalized.requirements.isEmpty &&
    receipt.normalized.coercions == receipt.original.coercions)
    "qualified normalization removed the distinct output-coercion obligation"
  let normalizedSource ← match normalizeOccurrence program coercedPlan coercedF none coercedF.source coercedId with
    | .ok source => pure source
    | .error error => throw (IO.userError s!"policy local normalization failed: {reprStr error}")
  assertTrue (normalizedSource.lookupExpression? coercedId == some receipt.normalized)
    "policy metadata read retained scheme-instance requirements"
  match normalizeOccurrence program coercedPlan coercedF none normalizedSource coercedId with
  | .ok repeated => assertTrue (repeated == normalizedSource) "local normalization was not idempotent"
  | .error error => throw (IO.userError s!"normalized metadata was rejected: {reprStr error}")
  let rawRequirements ← match SourceCompilationPlan.ordinaryOwnedRequirements? receipt.normalized with
    | some requirements => pure requirements
    | none => throw (IO.userError "normalized coercion requirement inventory is invalid")
  let raw := { receipt.normalized with
    type := receipt.normalized.rawType
    requirements := rawRequirements
    coercions := [] }
  let rawSource := { normalizedSource with nodes := normalizedSource.nodes.map fun
    | .expression node => .expression (if node.id == coercedId then raw else node)
    | .statement node => .statement node }
  match normalizeOccurrence program coercedPlan coercedF none rawSource coercedId with
  | .ok unchanged => assertTrue (unchanged == rawSource) "coercion-child raw metadata was replaced by post-coercion metadata"
  | .error error => throw (IO.userError s!"authentic raw local view rejected: {reprStr error}")
  let erasedSource := { normalizedSource with nodes := normalizedSource.nodes.map fun
    | .expression node => .expression (if node.id == coercedId then { node with requirements := [] } else node)
    | .statement node => .statement node }
  match normalizeOccurrence program coercedPlan coercedF none erasedSource coercedId with
  | .error (.occurrenceMismatch _) => pure ()
  | _ => throw (IO.userError "a forged erased coercion obligation was accepted")

  let nestedPlan ← plan program "nested"
  let nestedCatalog ← catalog checked nestedPlan
  let outer ← binding nestedCatalog "outer"
  let inner ← binding nestedCatalog "inner"
  assertTrue (outer.instances.length == 2 && inner.instances.length == 2) "nested qualified contexts disappeared"
  for outerInstance in outer.instances do
    let outerPrepared ← prepared program nestedPlan outerInstance
    assertTrue (outerPrepared.witnesses.length == 1) "outer local evidence was not retained"
    let innerInstance ← match inner.atContext outerPrepared.substitution with
      | [candidate] => pure candidate
      | _ => throw (IO.userError "nested qualified bundle matched another outer context")
    let innerPrepared ← prepared program nestedPlan innerInstance (some outerPrepared)
    assertTrue (innerPrepared.witnesses.length == 2 && innerPrepared.substitution == innerInstance.origin.substitution)
      "nested receipt lost the inherited dictionary or full cumulative context"
    checkCalls innerPrepared
    assertTrue (innerPrepared.caller.function.solvedRequirements.map (·.id) == innerInstance.origin.solvedRequirements.map (·.id))
      "nested evidence rebinding changed ledger identities"

  let first ← match f.instances with
    | first :: _ => pure first
    | [] => throw (IO.userError "qualified instances disappeared")
  let forgedLedger := { first with origin := { first.origin with solvedRequirements := [] } }
  match prepare program qualifiedPlan forgedLedger with
  | .error (.originMismatch _) => pure ()
  | _ => throw (IO.userError "a caller erased the original qualified ledger")
  let forgedSource := { first with origin := { first.origin with source := { first.origin.source with nodes := [] } } }
  match prepare program qualifiedPlan forgedSource with
  | .error (.originMismatch _) => pure ()
  | _ => throw (IO.userError "a fabricated local source obtained an evidence receipt")
  let forgedContext := { first with origin := { first.origin with localInstance :=
    { first.origin.localInstance with substitution := [] } } }
  match prepare program qualifiedPlan forgedContext with
  | .error (.instanceMismatch _) => pure ()
  | _ => throw (IO.userError "an undiscovered local substitution obtained an evidence receipt")
  let foreignParent ← prepared program nestedPlan (← match outer.instances with
    | first :: _ => pure first
    | [] => throw (IO.userError "outer instances disappeared"))
  match prepare program qualifiedPlan first (some foreignParent) with
  | .error (.parentMismatch _) => pure ()
  | _ => throw (IO.userError "an unrelated caller's dictionary entered a local instance")
  IO.println "qualified local evidence, nested dictionaries and retained obligation identities GREEN"

end Tests.SourceCoreLocalEvidence
