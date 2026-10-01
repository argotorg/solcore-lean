import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualProxies
import Solcore.Frontend.SourceCoreCompatibleFunctions
import Solcore.Frontend.SourceCoreCallableIndexedFrames
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Real contextual proxy emissions preserve original metadata, including
staging inside a proxy. Retained-IR negative cases distinguish raw type and
registry authentication from their shared native identity. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreCompatibleExpressionProxies
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleExpressionProxies CompatiblePayload

/-- The actual leaf receipt supplies an independent source trace and typed
finite Core execution for arbitrary ambient definitions and stores. -/
theorem accepted_finite
    {values : ValuesContext} {child : Child} {fuel : Nat} {source : TypedSource} {scope : Scope}
    {id : ExpressionId} {node : ExpressionNode} {inner : TypeSystem.Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node) (form : node.form = .proxy inner)
    (accepted : SourceCoreCompatibleDataExpressions.lowerWithReasons (fuel + 1) values child source scope id reasonAt = .ok lowered)
    (ambient : AmbientDefinitions values.checked.catalog.definitions)
    (program : SourceSemantics.Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap) (actual : Core.Environment)
    (store : Store) (ξ : Renaming) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap id (.proxy inner) heap ∧
    HasType [] lowered.expression (LanguageResult.resultType lowered.type) ambient.definitions ∧
    ∃ result, Evaluates actual store (lowered.expression.rename ξ) result store := by
  obtain ⟨owner, header, rfl, receipt⟩ := proxy_of_lower found form accepted
  exact ⟨receipt.source_evaluates program context evidence environment heap,
    receipt.hasType ambient [], _, receipt.native_evaluates actual store ξ⟩

private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function word() returns (@Word) { return @Word; }",
    "function boolean() returns (@Bool) { return @Bool; }",
    "function integer() returns (@integer) { return @integer; }",
    "function parent() returns (@Word) { let make = lam(value) { return @Word; }; return make(true); }"
  ]}] }

private def replace (source : TypedSource) (node : ExpressionNode) : TypedSource :=
  { source with nodes := source.nodes.map fun
    | .expression old => if old.id = node.id then .expression node else .expression old
    | .statement old => .statement old }

private def inspectNode {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared checked)
    (values : ValuesContext) (same : values.checked = checked)
    (source : TypedSource) (owner : SourceSpecialization.SpecializationKey)
    (parent : Option SourceCoreLocalEvidence.Prepared) (solved : List SolvedRequirement)
    (node : ExpressionNode) (inner : TypeSystem.Ty) (form : node.form = .proxy inner) : IO (Ty × Word) := do
  let representation := SourceCoreCompatibleFunctions.representation values 100
  let diagnostics ← match prepared.diagnostics with
    | some diagnostics => pure diagnostics.program | none => throw (IO.userError "proxy diagnostics missing")
  let own ← match diagnostics.base.find? owner with
    | some own => pure own | none => throw (IO.userError "proxy owner missing")
  let context : SourceCoreFunctions.Context := {
    plan := prepared.plan, owner, globals := prepared.globals, administrativePrefix := 1,
    solvedRequirements := solved, internalReason := Word.zero }
  let reasonAt := diagnostics.reasonAt owner
  if found : source.lookupExpression? node.id = some node then
    if requirements : node.requirements = [] then
      if coercions : node.coercions = [] then
        if notInitializer : prepared.locals.bindings.find? (fun binding => decide (binding.caller = owner ∧ binding.initializer = node.id)) = none then
          match accepted : SourceCoreGeneralFunctions.lowerContextualExpression prepared.sourceProgram representation
              checked.signatures prepared.locals prepared.contexts own.assignments diagnostics context prepared.callableContext
              parent none 100 source [] node.id reasonAt with
          | .error error => throw (IO.userError s!"actual contextual proxy rejected: {reprStr error}")
          | .ok lowered =>
            have receipt : Certificate values source [] node.id lowered := certificate_of_contextual
              found form requirements coercions notInitializer rfl rfl accepted
            let _receipt := receipt
            let (payload, header) ← match lowered.expression with
              | .inRight .word (.construct tag (.word header)) => pure (Core.Value.constructed tag (.word header), header)
              | _ => throw (IO.userError "proxy carrier shape changed")
            let decoded ← get "proxy raw decode" (SourceCoreCompatibleValues.decode 100 values node.type payload)
            assertTrue (decoded == .proxy inner) "proxy inner metadata changed"
            assertTrue (values.registry.lookup header == some (.proxy inner)) "proxy header is not the raw inner type"
            let frame : SourceCoreCallableIndexedFrames.Layout := ⟨⟨checked.catalog.definitions.length⟩⟩
            let frameValue := Core.Value.constructed frame.empty .unit
            let code := Expr.letE (.construct frame.empty .unit)
              (.letE (.newCell (.function .unit frame.type) (.lambda .unit frame.type (.var 1)))
                (.letE (.integer 91) (lowered.expression.weakenAt 0 |>.weakenAt 0 |>.weakenAt 0)))
            let native : Core.Program := ⟨LanguageResult.resultType lowered.type, code,
              checked.catalog.definitions ++ [frame.definition]⟩
            assertTrue native.check "proxy failed actual ambient checker"
            for fuel in [0, 2, 1000] do
              let result := match native.runStateful fuel with
                | .outOfFuel checkpoint => Core.runStateful 1000 checkpoint
                | other => other
              match result with
              | .done value store =>
                assertTrue (value == .inRight .word payload) "proxy native result changed"
                assertTrue (store == [.closure .unit frame.type (.var 1) [frameValue]]) "proxy changed ambient closure store"
              | other => throw (IO.userError s!"proxy did not complete: {reprStr other}")
            let _same := same
            pure (lowered.type, header)
        else throw (IO.userError "unexpected specialized proxy initializer")
      else throw (IO.userError "unexpected proxy coercion")
    else throw (IO.userError "unexpected proxy requirement")
  else throw (IO.userError "proxy occurrence missing")

private def inspect {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared checked) (source : TypedSource)
    (owner : SourceSpecialization.SpecializationKey) (parent : Option SourceCoreLocalEvidence.Prepared)
    (solved : List SolvedRequirement) : IO Nat := do
  let mut count := 0
  for entry in source.nodes do
    match entry with
    | .expression node =>
      match form : node.form with
      | .proxy inner =>
        let _ ← inspectNode prepared (.initial checked) rfl source owner parent solved node inner form
        count := count + 1
      | _ => pure ()
    | _ => pure ()
  pure count

def run : IO Unit := do
  let program ← get "proxy source checker" (checkProgram workspace)
  let roots ← ["word", "boolean", "integer", "parent"].mapM fun name =>
    match program.signatures.functions.find? (·.name == name) with
    | some signature => pure (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
    | none => throw (IO.userError s!"proxy root missing: {name}")
  let plan ← match SourceSpecializationWorklist.run program roots 256 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"proxy specialization: {reprStr other}")
  let automatic ← get "proxy actual factory" (SourceCoreCompatibleFunctions.prepare program plan 300)
  let mut count := 0
  for function in automatic.prepared.functions do
    count := count + (← inspect automatic.prepared function.specialized.function.typedBody
      function.signature.key none function.specialized.function.solvedRequirements)
  let mut contextual := 0
  for parent in automatic.prepared.contexts do
    if !parent.substitution.isEmpty then
      contextual := contextual + (← inspect automatic.prepared parent.source parent.caller.key
        (some parent) parent.caller.function.solvedRequirements)
  assertTrue (count ≥ 3 && contextual > 0) "proxy root or full-parent coverage missing"
  let wordId ← match program.signatures.functions.find? (·.name == "word") with
    | some signature => pure signature.id | none => throw (IO.userError "word root missing")
  let function ← match automatic.prepared.functions.find? (·.signature.key.declaration == wordId) with
    | some function => pure function | none => throw (IO.userError "word function missing")
  let source := function.specialized.function.typedBody
  let node ← match source.nodes.findSome? fun
    | .expression node => match node.form with | .proxy _ => some node | _ => none
    | _ => none with
    | some node => pure node | none => throw (IO.userError "word proxy missing")
  let original := SourceCoreCompatibleValues.Context.initial automatic.checked
  let rawInner := TypeSystem.Ty.comptime .word
  let rawNode := { node with type := .proxy rawInner, form := .proxy rawInner }
  let rawSource := replace source rawNode
  let encoded ← get "raw proxy registry" (SourceCoreCompatibleValues.encode 100 original (.proxy rawInner) (.proxy rawInner))
  let raw ← inspectNode automatic.prepared encoded.context rfl rawSource function.signature.key none
    function.specialized.function.solvedRequirements rawNode rawInner rfl
  let canonicalNode := { node with type := .proxy .word, form := .proxy .word }
  let canonical ← inspectNode automatic.prepared encoded.context rfl (replace source canonicalNode) function.signature.key none
    function.specialized.function.solvedRequirements canonicalNode .word rfl
  assertTrue (raw.1 == canonical.1 && raw.2 != canonical.2) "raw proxy metadata collapsed to native identity"
  let child : Child := fun _ _ _ id _ => .error (.unsupportedExpression id (.tuple []))
  let badRaw := { rawNode with type := .proxy .word }
  let badOuter := { canonicalNode with type := .comptime (.proxy .word) }
  let lower := fun values source => SourceCoreCompatibleDataExpressions.lowerWithReasons 100 values child source [] node.id (fun _ => Word.zero)
  assertTrue ((lower encoded.context (replace source badRaw)).toOption.isNone) "mismatched raw proxy type accepted"
  assertTrue ((lower original rawSource).toOption.isNone) "unregistered raw metadata accepted"
  assertTrue ((lower encoded.context (replace source badOuter)).toOption.isNone) "outer staging bypassed ordinary raw type check"
  IO.println "actual contextual proxies: raw/staged headers, full parent, malformed metadata, ambient captures and resume GREEN"

end Tests.SourceCoreCompatibleExpressionProxies
