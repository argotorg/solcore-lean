import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualLiterals
import Solcore.Frontend.SourceCoreCompatibleFunctions
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Actual root and specialized-parent literal emissions are certified before
execution. Both numeric targets, Unit, Bool, legacy Word spelling, malformed
retained evidence and exact store preservation are exercised. Unary minus is
outside the atomic certificate. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false
namespace Tests.SourceCoreCompatibleExpressionLiterals
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleExpressionLiterals CompatiblePayload GeneralHeap ReadOnly

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"compatible_literals", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "compatible_literals.solc"⟩, 0, 4⟩
private def id : ExpressionId := ⟨⟨owner, 0⟩⟩
private def boolNode : ExpressionNode := { id, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def boolSource : TypedSource := { owner, inputs := [], roots := [.expression id], nodes := [.expression boolNode] }
private def boolCode : SourceCoreBasic.LoweredExpr := ⟨.bool, LanguageResult.success (.bool true)⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def sourceContext : SourceSemantics.Context := .ofSignatures signatures
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private theorem valid : ContextValid [] sourceContext [] := by
  refine ⟨rfl, ⟨?_, ?_⟩, ?_⟩
  · simp [RequirementIdsUnique, sourceContext, SourceSemantics.Context.ofSignatures]
  · intro requirement member
    simp [sourceContext, SourceSemantics.Context.ofSignatures] at member
  · constructor
    · intro goal evidence found; cases found
    · intro predicate member
      simp [sourceContext, SourceSemantics.Context.ofSignatures] at member

private theorem boolAccepted (values : SourceCoreCompatibleValues.Context) (compilation : SourceCoreFunctions.Context)
    (body : SourceCoreFunctions.BodyLowerer)
    (read : SourceCoreCompatibleDataExpressions.readExpression values.checked boolSource id = .ok (boolNode, .bool)) :
    SourceCoreFunctions.lowerExpressionWithPolicy (SourceCoreCompatibleDataExpressions.functionPolicy 10 values)
      body 10 {compilation with solvedRequirements := []} boolSource [] id (fun _ => Word.zero) = .ok boolCode := by
  have found : boolSource.lookupExpression? id = some boolNode := rfl
  have sameOwner : id.occurrence.owner = boolSource.owner := rfl
  rw [SourceCoreFunctions.lowerExpressionWithPolicy]
  simp only [SourceCoreCompatibleDataExpressions.functionPolicy, sameOwner, ne_eq, not_true_eq_false,
    ↓reduceIte, found, bind, Except.bind, pure, Except.pure]
  simp only [boolNode]
  rw [read]
  simp only [bind, Except.bind, boolNode]
  unfold SourceCoreCompatibleDataExpressions.leafLowerer
  rw [read]
  change SourceCoreBasic.lowerExpression 10 boolSource [] id Word.zero = .ok boolCode
  rfl


/-- Completed actual Bool code reconstructs its independent source trace even
with arbitrary ambient closures in the represented heap and inserted slots. -/
theorem bool_reflects {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    (values : SourceCoreCompatibleValues.Context) (compilation : SourceCoreFunctions.Context)
    (body : SourceCoreFunctions.BodyLowerer)
    (read : SourceCoreCompatibleDataExpressions.readExpression values.checked boolSource id = .ok (boolNode, .bool))
    {mapping world administrative environment canonical actual before store ξ value after}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world
      administrative [] environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before sourceContext.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (evaluated : Evaluates actual store (boolCode.expression.rename ξ) value after) :
    ∃ outcome sourceAfter finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program sourceContext [] boolSource environment before id outcome sourceAfter ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel checked registry functions)
        finalMap finalWorld .bool boolCode.type (fun _ _ => False) outcome value ∧
      CompatibleAmbientHeap.HeapRepresents checked registry functions finalMap finalWorld sourceAfter after ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap after ∧ Dynamic.HeapMetadataExtend before sourceAfter := by
  have receipt : Certificate [] boolSource id boolCode := of_functions (values := values)
    (by rfl) (.bool _ _) (by intro impossible; cases impossible)
    (by intros; rfl) rfl rfl (boolAccepted values compilation body read)
  exact reflects functions program sourceContext [] valid boolSource (fun _ _ => False)
    receipt (by rfl) environments heaps locals agrees evaluated

private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def huge : Nat := 115792089237316195423570985008687907853269984665640564039457584007913129639937
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function unit() { return (); }",
    "function boolean() returns (Bool) { return true; }",
    "function word() returns (Word) { return 37; }",
    s!"function wordWrap() returns (Word) \{ return {huge}; }",
    s!"function big() returns (integer) \{ return {huge}; }",
    "function parent(seed: Word) returns (Word) { let echo = lam(value) { return seed + 37; }; return echo(true); }"
  ]}] }

private def scalar? : Expr → Option Core.Value
  | .unit => some .unit | .bool b => some (.bool b) | .word w => some (.word w)
  | .integer n => some (.integer n) | _ => none

private def inspectNode {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared checked) (source : TypedSource)
    (owner : SourceSpecialization.SpecializationKey) (parent : Option SourceCoreLocalEvidence.Prepared)
    (solved : List SolvedRequirement) (node : ExpressionNode) (atomic : Atomic node.form) : IO (Option Ty) := do
  let values := SourceCoreCompatibleValues.Context.initial checked
  let representation := SourceCoreCompatibleFunctions.representation values 100
  let diagnostics ← match prepared.diagnostics with
    | some diagnostics => pure diagnostics.program | none => throw (IO.userError "literal diagnostics missing")
  let own ← match diagnostics.base.find? owner with
    | some own => pure own | none => throw (IO.userError "literal root diagnostics missing")
  let context : SourceCoreFunctions.Context := {
    plan := prepared.plan, owner, globals := prepared.globals, administrativePrefix := 1,
    solvedRequirements := solved, internalReason := Word.zero }
  let reasonAt := diagnostics.reasonAt owner
  if found : source.lookupExpression? node.id = some node then
    if requirements : node.requirements = owned node.form then
      if coercions : node.coercions = [] then
        if notInitializer : prepared.locals.bindings.find? (fun binding => decide (binding.caller = owner ∧ binding.initializer = node.id)) = none then
          if unitType : node.form = .tuple [] → node.type = .unit then
            match accepted : SourceCoreGeneralFunctions.lowerContextualExpression prepared.sourceProgram representation
                checked.signatures prepared.locals prepared.contexts own.assignments diagnostics context prepared.callableContext
                parent none 100 source [] node.id reasonAt with
            | .error error => throw (IO.userError s!"actual contextual literal rejected: {reprStr error}")
            | .ok lowered =>
              have receipt : Certificate solved source node.id lowered := of_contextual (values := values)
                found atomic unitType requirements coercions notInitializer rfl rfl accepted
              let _receipt := receipt
              let expected ← match lowered.expression with
                | .inRight .word payload => match scalar? payload with
                  | some value => pure (.inRight .word value)
                  | none => throw (IO.userError "atomic output is not a scalar")
                | _ => throw (IO.userError "literal changed language result carrier")
              match node.form with
              | .integerLiteral _ resolution =>
                match resolution.targetType, expected with
                | .word, .inRight .word (.word value) =>
                  assertTrue (value == Word.ofNatModulo resolution.rawValue) "Word literal lost modulo meaning"
                | .integer, .inRight .word (.integer value) =>
                  assertTrue (value == Int.ofNat resolution.rawValue) "Integer literal lost unbounded meaning"
                | _, _ => throw (IO.userError "numeric target changed")
                let malformed := { node with requirements := [] }
                let bad := { source with nodes := source.nodes.map fun
                  | .expression old => if old.id = node.id then .expression malformed else .expression old
                  | .statement old => .statement old }
                assertTrue ((SourceCoreGeneralFunctions.lowerContextualExpression prepared.sourceProgram representation
                  checked.signatures prepared.locals prepared.contexts own.assignments diagnostics context prepared.callableContext
                  parent none 100 bad [] node.id reasonAt).toOption.isNone) "missing numeric requirement was accepted"
              | _ => pure ()
              let code := .letE (.newCell (.function .unit .unit) (.lambda .unit .unit .unit)) (lowered.expression.weakenAt 0)
              let native : Core.Program := ⟨LanguageResult.resultType lowered.type, code, checked.catalog.definitions⟩
              assertTrue native.check "actual literal failed Core checker"
              for fuel in [0, 2, 1000] do
                let completed := match native.runStateful fuel with
                  | .outOfFuel checkpoint => Core.runStateful 1000 checkpoint
                  | other => other
                match completed with
                | .done value store =>
                  assertTrue (value == expected && store == [.closure .unit .unit .unit []]) "literal modified administrative closure store"
                | other => throw (IO.userError s!"literal did not complete: {reprStr other}")
              pure (some lowered.type)
          else pure none
        else pure none
      else pure none
    else pure none
  else pure none

private def inspect {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared checked) (source : TypedSource)
    (owner : SourceSpecialization.SpecializationKey) (parent : Option SourceCoreLocalEvidence.Prepared)
    (solved : List SolvedRequirement) : IO (List Ty) := do
  let mut types := []
  for entry in source.nodes do
    match entry with
    | .expression node =>
      let result ← match form : node.form with
        | .tuple [] => inspectNode prepared source owner parent solved node (form ▸ .unit)
        | .reference name (.builtinBoolean value) => inspectNode prepared source owner parent solved node (form ▸ .bool name value)
        | .literal value => inspectNode prepared source owner parent solved node (form ▸ .word value)
        | .integerLiteral value resolution => inspectNode prepared source owner parent solved node (form ▸ .integer value resolution)
        | _ => pure none
      if let some type := result then types := types ++ [type]
    | _ => pure ()
  pure types

def run : IO Unit := do
  let program ← get "literal source checker" (checkProgram workspace)
  let roots ← ["unit", "boolean", "word", "wordWrap", "big", "parent"].mapM fun name =>
    match program.signatures.functions.find? (·.name == name) with
    | some signature => pure (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
    | none => throw (IO.userError s!"literal root missing: {name}")
  let plan ← match SourceSpecializationWorklist.run program roots 256 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"literal specialization: {reprStr other}")
  let automatic ← get "actual literal compatible factory" (SourceCoreCompatibleFunctions.prepare program plan 300)
  let mut types := []
  for function in automatic.prepared.functions do
    types := types ++ (← inspect automatic.prepared function.specialized.function.typedBody
      function.signature.key none function.specialized.function.solvedRequirements)
  let wordId ← match program.signatures.functions.find? (·.name == "word") with
    | some signature => pure signature.id | none => throw (IO.userError "legacy literal declaration missing")
  let wordFunction ← match automatic.prepared.functions.find? (·.signature.key.declaration == wordId) with
    | some function => pure function | none => throw (IO.userError "legacy literal owner missing")
  let original := wordFunction.specialized.function.typedBody
  let numeric ← match original.nodes.findSome? fun
    | .expression node => match node.form with | .integerLiteral .. => some node | _ => none
    | _ => none with
    | some node => pure node | none => throw (IO.userError "legacy literal occurrence missing")
  let legacy := { numeric with form := .literal (.decimal "37"), requirements := [], coercions := [] }
  let legacySource := { original with nodes := original.nodes.map fun
    | .expression old => if old.id = legacy.id then .expression legacy else .expression old
    | .statement old => .statement old }
  let legacyResult ← inspectNode automatic.prepared legacySource wordFunction.signature.key none
    wordFunction.specialized.function.solvedRequirements legacy (.word _)
  assertTrue (legacyResult == some .word) "legacy Word-spelling branch missing"
  let mut contextual := []
  for parent in automatic.prepared.contexts do
    if !parent.substitution.isEmpty then
      contextual := contextual ++ (← inspect automatic.prepared parent.source parent.caller.key
        (some parent) parent.caller.function.solvedRequirements)
  for required in [Ty.unit, .bool, .word, .integer] do
    assertTrue (types.contains required) s!"literal target missing: {reprStr required}"
  assertTrue (!contextual.isEmpty) "full parent context literal missing"
  IO.println "actual contextual literal certificates: Unit/Bool/Word/Integer, parent substitution, malformed evidence and resume GREEN"

end Tests.SourceCoreCompatibleExpressionLiterals
