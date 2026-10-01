import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualReads
import Solcore.Frontend.SourceCoreCompatibleFunctions
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! The actual shared traversal is exercised at named roots and inside a
prepared generic parent with a nonempty full substitution. Both static read
receipts are extracted from its actual successful result before native runs.
The source typing premise of the semantic bridge remains independent. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleContextualReads
open Solcore Core Frontend SourceInference SourceSemantics.CoreLowering
open CompatibleExpressionReads

private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def word (n : Nat) : Word := Word.ofNatModulo n
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function root(value: Bool) returns (Bool) { return value; }",
    "function parent(seed: Word) returns (Word) { let echo = lam(value) { return seed; }; return echo(true); }",
    "function lazy() returns (mapping(Word => Word)) { let table: mapping(Word => Word); return table; }"
  ]}] }

private def inspect {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared checked) (source : TypedSource)
    (owner : SourceSpecialization.SpecializationKey) (parent : Option SourceCoreLocalEvidence.Prepared)
    (solved : List SolvedRequirement) : IO Nat := do
  let values := SourceCoreCompatibleValues.Context.initial checked
  let representation := SourceCoreCompatibleFunctions.representation values 100
  let diagnostics ← match prepared.diagnostics with
    | some diagnostics => pure diagnostics.program
    | none => throw (IO.userError "contextual read diagnostics missing")
  let own ← match diagnostics.base.find? owner with
    | some own => pure own | none => throw (IO.userError "contextual root diagnostics missing")
  let context : SourceCoreFunctions.Context := {
    plan := prepared.plan, owner, globals := prepared.globals, administrativePrefix := 1,
    solvedRequirements := solved, internalReason := Word.zero }
  let reasonAt := diagnostics.reasonAt owner
  let mut count := 0
  for entry in source.nodes do
    match entry with
    | .expression node =>
      match form : node.form with
      | .reference _name (.local binder) =>
        if found : source.lookupExpression? node.id = some node then
          if requirements : node.requirements = [] then
            if coercions : node.coercions = [] then
              if ordinary : prepared.locals.bindings.any (fun binding => decide (binding.caller = owner ∧ binding.binder.id = binder)) = false then
                if notInitializer : prepared.locals.bindings.find? (fun binding => decide (binding.caller = owner ∧ binding.initializer = node.id)) = none then
                  let declared ← get "ordinary source binder" (SourceCoreDataPlaces.rootBinder source binder)
                  let type ← get "ordinary native type" (checked.catalog.project declared.scheme.body)
                  let scope := [(binder, type)]
                  match accepted : SourceCoreGeneralFunctions.lowerContextualExpression prepared.sourceProgram representation
                      checked.signatures prepared.locals prepared.contexts own.assignments diagnostics context prepared.callableContext
                      parent none 100 source scope node.id reasonAt with
                  | .error error => throw (IO.userError s!"actual contextual read rejected: {reprStr error}")
                  | .ok lowered =>
                    have receipts := contextual_read_receipts (readFuel := 100) (values := values)
                      found form requirements coercions ordinary notInitializer rfl rfl accepted
                    have staticReceipt : Nonempty (Certificate 100 values source scope node.id (reasonAt node.id) lowered.expression) :=
                      of_accepted receipts.2
                    let _receipt := staticReceipt
                    let (_, projected) ← get "retained read metadata" (SourceCoreCompatibleDataExpressions.readExpression checked source node.id)
                    assertTrue (projected == lowered.type && type == lowered.type) "contextual read changed native type"
                    let direct ← get "direct compatible read" (SourceCoreCompatibleDataExpressions.lowerRead 100 values source scope node.id (reasonAt node.id))
                    assertTrue (direct == lowered.expression) "contextual traversal changed ordinary read code"
                    let initializers : List (Expr × Core.Value) ← match declared.scheme.body with
                      | .bool => pure [(OptionalCell.allocateInitialized type (.bool true), .inRight .word (.bool true)),
                          (OptionalCell.allocate type, .inLeft type (.word (reasonAt node.id)))]
                      | .word => pure [(OptionalCell.allocateInitialized type (.word (word 23)), .inRight .word (.word (word 23))),
                          (OptionalCell.allocate type, .inLeft type (.word (reasonAt node.id)))]
                      | .mapping key value => do
                        let encoded ← get "empty mapping" (SourceCoreCompatibleValues.encode 100 values declared.scheme.body (.mapping key value []))
                        pure [(OptionalCell.allocate type, .inRight .word encoded.value)]
                      | _ => throw (IO.userError s!"unexpected ordinary fixture type: {reprStr declared.scheme.body}")
                    for (initializer, expected) in initializers do
                      let native : Core.Program := ⟨LanguageResult.resultType lowered.type, .letE initializer lowered.expression, checked.catalog.definitions⟩
                      assertTrue native.check "actual contextual read failed Core checker"
                      for fuel in [0, 2, 1000] do
                        let completed := match native.runStateful fuel with
                          | .outOfFuel checkpoint => Core.runStateful 1000 checkpoint
                          | other => other
                        match completed with
                        | .done value store =>
                          assertTrue (value == expected && store.length == 1) "actual contextual read outcome/effect mismatch"
                        | other => throw (IO.userError s!"actual contextual read did not complete: {reprStr other}")
                    count := count + 1
      | _ => pure ()
    | _ => pure ()
  pure count

def run : IO Unit := do
  let program ← get "contextual source checker" (checkProgram workspace)
  let roots ← ["root", "parent", "lazy"].mapM fun name =>
    match program.signatures.functions.find? (·.name == name) with
    | some signature => pure (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
    | none => throw (IO.userError "contextual fixture root missing")
  let plan ← match SourceSpecializationWorklist.run program roots 256 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"contextual specialization: {reprStr other}")
  let automatic ← get "actual compatible factory" (SourceCoreCompatibleFunctions.prepare program plan 300)
  let mut rootReads := 0
  for function in automatic.prepared.functions do
    rootReads := rootReads + (← inspect automatic.prepared function.specialized.function.typedBody
      function.signature.key none function.specialized.function.solvedRequirements)
  let mut contextualReads := 0
  for parent in automatic.prepared.contexts do
    if !parent.substitution.isEmpty then
      contextualReads := contextualReads + (← inspect automatic.prepared parent.source parent.caller.key
        (some parent) parent.caller.function.solvedRequirements)
  assertTrue (rootReads ≥ 3) "named root read receipts missing"
  assertTrue (contextualReads > 0) "nonempty full parent context read receipt missing"
  IO.println "actual contextual ordinary reads: named roots, full parent substitution, initialization, fault and resume GREEN"

end Tests.SourceCoreCompatibleContextualReads
