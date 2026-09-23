import Solcore.Frontend.SourceRuntimeLinking

/-! End-to-end regressions for finite whole-program specialization discovery. -/

set_option autoImplicit false

namespace Tests.SourceSpecializationWorklist

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.TypeSystem

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{
    path := "main.solc"
    content := String.intercalate "\n" [
      "trait Eq<T> {}",
      "impl Eq<Word> {}",
      "function identity<T>(value: T) returns (T) { return value; }",
      "function twice<T>(value: T) returns (T) { return identity(identity(value)); }",
      "function first<T>(value: T) returns (T) { return value; }",
      "function second<T>(value: T) returns (T) { return value; }",
      "function nested(value: Word) returns (Word) { return first(second(value)); }",
      "function pick<A, B>(left: A, right: B) returns (A) { return left; }",
      "function select(left: Word, right: Bool) returns (Word) { return pick(left, right); }",
      "function loop<T>(value: T) returns (T) { return loop(value); }",
      "function cycleLeft<T>(value: T) returns (T) { return cycleRight(value); }",
      "function cycleRight<U>(value: U) returns (U) { return cycleLeft(value); }",
      "function grow<T>(value: T) { grow((value, value)); return; }",
      "function keep<T>(value: T) returns (T) where T: Eq { return value; }",
      "function constrained(value: Word) returns (Word) { return keep(value); }",
      "function asValue() returns (function(Word) returns (Word)) { return identity; }",
      "function apply(f: function(Word) returns (Word), value: Word) returns (Word) { return f(value); }",
      "function applyProduct(f: function((Word, Bool)) returns (Word), pair: (Word, Bool)) returns (Word) { return f(pair); }",
      "function applySplit(f: function(Word, Bool) returns (Word), left: Word, right: Bool) returns (Word) { return f(left, right); }"
    ]
  }]
  externalLibraries := []
}

private def checkedProgram : IO CheckedProgram := do
  match checkProgram workspace with
  | .ok program => pure program
  | .error errors => throw (IO.userError
      s!"specialization-worklist fixture failed checking: {reprStr errors}")

private def signatureNamed (program : CheckedProgram) (name : String) :
    IO ProgramFunctionSignature := do
  match program.signatures.functions.filter fun signature =>
      signature.name == name with
  | [signature] => pure signature
  | signatures => throw (IO.userError
      s!"expected one signature named `{name}`, found {signatures.length}")

private def functionFor (program : CheckedProgram)
    (signature : ProgramFunctionSignature) : IO CheckedFunction := do
  match program.functions.filter fun function =>
      function.declaration == signature.id with
  | [function] => pure function
  | functions => throw (IO.userError
      s!"expected one body named `{signature.name}`, found {functions.length}")

private def replaceFunction (program : CheckedProgram)
    (replacement : CheckedFunction) : CheckedProgram := {
  program with
  functions := program.functions.map fun function =>
    if function.declaration == replacement.declaration then
      replacement
    else
      function
}

private def firstDirectCall? : List Node → Option (ExpressionId × ExpressionId)
  | [] => none
  | .expression { id, form := .call callee _ (.declaration _), .. } :: _ =>
      some (id, callee)
  | _ :: rest => firstDirectCall? rest

private def firstIndirectCall? :
    List Node → Option (ExpressionNode × IndirectCallResolution)
  | [] => none
  | .expression node@{ form := .call _ _ (.indirect metadata), .. } :: _ =>
      some (node, metadata)
  | _ :: rest => firstIndirectCall? rest

private def setExpressionType (nodes : List Node) (target : ExpressionId)
    (type : Ty) : List Node :=
  nodes.map fun node => match node with
  | .expression expression =>
      if expression.id == target then
        .expression { expression with type }
      else
        node
  | .statement _ => node

private def setExpressionCoercions (nodes : List Node) (target : ExpressionId)
    (coercions : List CoercionStep) : List Node :=
  nodes.map fun node => match node with
  | .expression expression =>
      if expression.id == target then
        .expression { expression with coercions }
      else
        node
  | .statement _ => node

private def setIndirectMetadata (nodes : List Node) (target : ExpressionId)
    (metadata : IndirectCallResolution) : List Node :=
  nodes.map fun node => match node with
  | .expression expression =>
      if expression.id == target then
        match expression.form with
        | .call callee arguments (.indirect _) =>
            .expression {
              expression with
              form := .call callee arguments (.indirect metadata)
            }
        | _ => node
      else
        node
  | .statement _ => node

private def setDirectInstantiationMarkers (nodes : List Node)
    (call callee : ExpressionId) (parameterComptime : List Bool)
    (returnComptime : Bool) : List Node :=
  nodes.map fun node => match node with
  | .expression expression =>
      if expression.id == callee then
        match expression.form with
        | .reference name (.declaration instantiation) =>
            .expression {
              expression with
              form := .reference name (.declaration {
                instantiation with parameterComptime, returnComptime
              })
            }
        | _ => node
      else if expression.id == call then
        match expression.form with
        | .call target arguments (.declaration instantiation) =>
            .expression {
              expression with
              form := .call target arguments (.declaration {
                instantiation with parameterComptime, returnComptime
              })
            }
        | _ => node
      else
        node
  | .statement _ => node

private def eraseExpression (nodes : List Node)
    (target : ExpressionId) : List Node :=
  nodes.filter fun node => match node with
  | .expression expression => expression.id != target
  | .statement _ => true

private def monomorphicRequest (signature : ProgramFunctionSignature) :
    SourceSpecializationWorklist.Request := {
  declaration := signature.id
  parameterSubstitution := []
}

private def unaryRequest (signature : ProgramFunctionSignature) (type : Ty) :
    IO SourceSpecializationWorklist.Request := do
  match signature.scheme.parameters with
  | [parameter] => pure {
      declaration := signature.id
      parameterSubstitution := [(parameter, type)]
    }
  | parameters => throw (IO.userError
      s!"expected one generic parameter for `{signature.name}`, found {parameters.length}")

private def runOrThrow (label : String) (program : CheckedProgram)
    (requests : List SourceSpecializationWorklist.Request) (budget : Nat) :
    IO SourceSpecializationWorklist.Outcome := do
  match SourceSpecializationWorklist.run program requests budget with
  | .ok outcome => pure outcome
  | .error error => throw (IO.userError
      s!"{label}: worklist failed: {reprStr error}")

private def testBreadthFirstDiscovery (program : CheckedProgram) : IO Unit := do
  let identity ← signatureNamed program "identity"
  let twice ← signatureNamed program "twice"
  let request ← unaryRequest twice .word
  let twiceKey : SourceSpecialization.SpecializationKey := {
    declaration := twice.id
    arguments := [.word]
  }
  match ← runOrThrow "twice" program [request] 2 with
  | .complete plan =>
      assertTrue (decide (plan.seedKeys = [twiceKey] ∧
          plan.specializations.map (·.declaration) =
          [twice.id, identity.id]))
        "canonical roots or FIFO first-discovery order were not retained"
      assertTrue (decide (plan.specializations.map (·.key.arguments) =
          [[.word], [.word]]))
        "a nested direct-call instantiation did not specialize to Word"
      assertTrue (decide (plan.callEdges.length = 2 ∧
          (plan.callEdges.map (·.occurrence)).eraseDups.length = 2 ∧
          plan.callEdges.all fun edge =>
            edge.caller.declaration = twice.id ∧
            edge.callee.declaration = identity.id))
        "two syntactic calls to one canonical callee did not retain two edges"
      assertTrue plan.referenceEdges.isEmpty
        "direct-call callee children were duplicated as reference edges"
      match SourceCoreDirectLinking.validatePlan program plan with
      | .ok () => pure ()
      | .error error => throw (IO.userError
          s!"canonical complete plan failed replay validation: {reprStr error}")
  | outcome => throw (IO.userError
      s!"twice: expected a complete plan, found {reprStr outcome}")
  match ← runOrThrow "twice budget" program [request] 1 with
  | .budgetExhausted plan next pending =>
      assertTrue (decide (plan.specializations.length = 1 ∧
          plan.callEdges.length = 2 ∧ next.declaration = identity.id ∧
          next.arguments = [.word] ∧ pending.length = 2))
        "budget exhaustion did not expose the first unseen canonical key"
  | outcome => throw (IO.userError
      s!"twice budget: expected exhaustion, found {reprStr outcome}")
  match ← runOrThrow "duplicate roots" program [request, request] 2 with
  | .complete plan =>
      assertTrue (decide (plan.seedKeys = [twiceKey, twiceKey] ∧
          plan.specializations.length = 2 ∧ plan.callEdges.length = 2))
        "duplicate roots were lost or charged as duplicate specializations"
      match SourceCoreDirectLinking.validatePlan program plan with
      | .ok () => pure ()
      | .error error => throw (IO.userError
          s!"duplicate canonical roots failed replay validation: {reprStr error}")
  | outcome => throw (IO.userError
      s!"duplicate roots: expected a complete plan, found {reprStr outcome}")

private def testDerivedCanonicalization (program : CheckedProgram) : IO Unit := do
  let pick ← signatureNamed program "pick"
  let select ← signatureNamed program "select"
  match ← runOrThrow "select" program [monomorphicRequest select] 2 with
  | .complete plan =>
      match plan.specializations with
      | [_, specializedPick] =>
          assertTrue (decide (specializedPick.declaration = pick.id ∧
              specializedPick.key.arguments = [.word, .bool]))
            "derived raw substitution was not canonicalized in signature order"
      | specializations => throw (IO.userError
          s!"select: expected two specializations, found {specializations.length}")
  | outcome => throw (IO.userError
      s!"select: expected a complete plan, found {reprStr outcome}")

private def testTypedNodeOrder (program : CheckedProgram) : IO Unit := do
  let first ← signatureNamed program "first"
  let second ← signatureNamed program "second"
  let nested ← signatureNamed program "nested"
  match ← runOrThrow "nested" program [monomorphicRequest nested] 3 with
  | .complete plan =>
      assertTrue (decide (plan.specializations.map (·.declaration) =
          [nested.id, second.id, first.id] ∧
          plan.callEdges.map (·.callee.declaration) =
            [second.id, first.id]))
        "nested direct calls did not follow deterministic typed-node order"
  | outcome => throw (IO.userError
      s!"nested: expected a complete plan, found {reprStr outcome}")

private def testRecursiveKeys (program : CheckedProgram) : IO Unit := do
  let loop ← signatureNamed program "loop"
  let loopRequest ← unaryRequest loop .word
  match ← runOrThrow "loop" program [loopRequest] 1 with
  | .complete plan =>
      match plan.callEdges with
      | [edge] =>
          assertTrue (decide (plan.specializations.length = 1 ∧
              edge.caller = edge.callee))
            "same-key self recursion consumed another specialization"
      | edges => throw (IO.userError
          s!"loop: expected one self edge, found {edges.length}")
  | outcome => throw (IO.userError
      s!"loop: expected a complete plan, found {reprStr outcome}")
  let cycleLeft ← signatureNamed program "cycleLeft"
  let cycleRight ← signatureNamed program "cycleRight"
  let cycleRequest ← unaryRequest cycleLeft .word
  match ← runOrThrow "mutual cycle" program [cycleRequest] 2 with
  | .complete plan =>
      assertTrue (decide (plan.specializations.map (·.declaration) =
          [cycleLeft.id, cycleRight.id] ∧
          plan.callEdges.map (fun edge =>
            (edge.caller.declaration, edge.callee.declaration)) =
            [(cycleLeft.id, cycleRight.id), (cycleRight.id, cycleLeft.id)]))
        "same-key mutual recursion did not close after two specializations"
  | outcome => throw (IO.userError
      s!"mutual cycle: expected a complete plan, found {reprStr outcome}")
  let grow ← signatureNamed program "grow"
  let growRequest ← unaryRequest grow .word
  match ← runOrThrow "grow" program [growRequest] 2 with
  | .budgetExhausted plan next _ =>
      let admitted := plan.specializations.map (·.key)
      assertTrue (decide (plan.specializations.length = 2 ∧
          plan.callEdges.length = 2 ∧ next.declaration = grow.id ∧
          next.arguments.length = 1) && !admitted.contains next)
        "type-growing recursion did not stop at the distinct-key budget"
  | outcome => throw (IO.userError
      s!"grow: expected exhaustion, found {reprStr outcome}")

private def testAssumptionPreservation (program : CheckedProgram) : IO Unit := do
  let keep ← signatureNamed program "keep"
  let constrained ← signatureNamed program "constrained"
  match ← runOrThrow "constrained" program
      [monomorphicRequest constrained] 2 with
  | .complete plan =>
      let specializedKeep := plan.specializations.find? fun specialized =>
        specialized.declaration == keep.id
      let specializedCaller := plan.specializations.find? fun specialized =>
        specialized.declaration == constrained.id
      match specializedKeep, specializedCaller with
      | some callee, some caller =>
          let hasImplementationEvidence :=
            caller.function.solvedRequirements.any fun requirement =>
              match requirement.evidence with
              | .implementation _ => true
              | .assumption _ => false
          assertTrue (decide (callee.key.arguments = [.word] ∧
              callee.assumptions.length = 1) && hasImplementationEvidence)
            "where predicate or solved caller evidence was consumed during discovery"
      | _, _ => throw (IO.userError
          "constrained: caller or keep<Word> specialization was not discovered")
  | outcome => throw (IO.userError
      s!"constrained: expected a complete plan, found {reprStr outcome}")

private def testFunctionValueReference (program : CheckedProgram) : IO Unit := do
  let identity ← signatureNamed program "identity"
  let asValue ← signatureNamed program "asValue"
  let function ← functionFor program asValue
  let reference ← match function.typedBody.nodes.findSome? fun node =>
      match node with
      | .expression expression@{
          form := .reference _ (.declaration instantiation), .. } =>
          if instantiation.declaration == identity.id then some expression else none
      | _ => none with
    | some reference => pure reference
    | none => throw (IO.userError
        "asValue: standalone declaration reference metadata was absent")
  match ← runOrThrow "asValue" program [monomorphicRequest asValue] 2 with
  | .complete plan =>
      match plan.referenceEdges with
      | [edge] =>
          assertTrue (decide (plan.specializations.map (·.declaration) =
              [asValue.id, identity.id] ∧ plan.callEdges = [] ∧
              edge.caller.declaration = asValue.id ∧
              edge.occurrence = reference.id ∧
              edge.callee.declaration = identity.id ∧
              edge.callee.arguments = [.word]))
            "standalone function reference did not retain its canonical edge"
      | edges => throw (IO.userError
          s!"asValue: expected one reference edge, found {edges.length}")
      let malformed : SourceSpecializationWorklist.Plan := {
        plan with referenceEdges := []
      }
      match SourceCoreDirectLinking.validatePlan program malformed with
      | .error (.referenceEdgesMismatch expected []) =>
          assertTrue (decide (expected = plan.referenceEdges))
            "reference-ledger rejection lost the canonical edge"
      | result => throw (IO.userError
          s!"direct plan validation accepted a missing reference edge: {reprStr result}")
      match SourceRuntimeLinking.link program (.complete malformed) with
      | .error (.invalidPlan
          (.referenceEdgesMismatch expected [])) =>
          assertTrue (decide (expected = plan.referenceEdges))
            "runtime linker lost the canonical reference ledger"
      | result => throw (IO.userError
          s!"runtime linker accepted a missing reference edge: {reprStr result}")
  | outcome => throw (IO.userError
      s!"asValue: expected a complete plan, found {reprStr outcome}")
  match ← runOrThrow "asValue budget" program
      [monomorphicRequest asValue] 1 with
  | .budgetExhausted plan next pending =>
      assertTrue (decide (plan.specializations.length = 1 ∧
          plan.callEdges = [] ∧ plan.referenceEdges.length = 1 ∧
          next.declaration = identity.id ∧ next.arguments = [.word] ∧
          pending.length = 1))
        "standalone function reference was absent from the FIFO frontier"
  | outcome => throw (IO.userError
      s!"asValue budget: expected exhaustion, found {reprStr outcome}")
  let malformedFunction : CheckedFunction := {
    function with
    typedBody := {
      function.typedBody with
      nodes := setExpressionType function.typedBody.nodes reference.id .bool
    }
  }
  match SourceSpecializationWorklist.run
      (replaceFunction program malformedFunction)
      [monomorphicRequest asValue] 2 with
  | .error (.calleeNodeTypeMismatch actual .bool _) =>
      assertTrue (actual == reference.id)
        "standalone reference mismatch lost its occurrence identity"
  | result => throw (IO.userError
      s!"malformed standalone reference metadata was accepted: {reprStr result}")

private def testIndirectCallBoundary (program : CheckedProgram) : IO Unit := do
  let apply ← signatureNamed program "apply"
  let function ← functionFor program apply
  let (call, metadata) ← match firstIndirectCall? function.typedBody.nodes with
    | some call => pure call
    | none => throw (IO.userError "apply: indirect call metadata was absent")
  assertTrue (decide (call.type = .word ∧ call.coercions = [] ∧
      metadata.argumentTypeBeforeCoercion = .word ∧
      metadata.argumentTypeAfterCoercion = .word ∧
      metadata.argumentCoercions = [] ∧
      metadata.hasValidArgumentCoercionPath))
    "apply: exact indirect arguments produced malformed call metadata"
  match SourceSpecializationWorklist.run program
      [monomorphicRequest apply] 1 with
  | .ok (.complete plan) =>
      assertTrue (decide (plan.specializations.length = 1 ∧
          plan.callEdges = [] ∧ plan.referenceEdges = []))
        "well-typed indirect call added a static target edge"
  | result => throw (IO.userError
      s!"well-typed indirect call was not accepted: {reprStr result}")
  let malformedMetadata := {
    metadata with argumentTypeAfterCoercion := Ty.bool
  }
  let malformedFunction : CheckedFunction := {
    function with
    typedBody := {
      function.typedBody with
      nodes := setIndirectMetadata function.typedBody.nodes call.id
        malformedMetadata
    }
  }
  match SourceSpecializationWorklist.run
      (replaceFunction program malformedFunction)
      [monomorphicRequest apply] 1 with
  | .error (.invalidIndirectArgumentCoercionPath actual metadata) =>
      assertTrue (actual == call.id && !metadata.hasValidArgumentCoercionPath)
        "invalid indirect metadata lost its call occurrence or path"
  | result => throw (IO.userError
      s!"malformed indirect coercion metadata was not rejected: {reprStr result}")
  let wrongBundleMetadata := {
    metadata with
    argumentTypeBeforeCoercion := Ty.bool
    argumentTypeAfterCoercion := Ty.bool
  }
  let wrongBundleFunction : CheckedFunction := {
    function with
    typedBody := {
      function.typedBody with
      nodes := setIndirectMetadata function.typedBody.nodes call.id
        wrongBundleMetadata
    }
  }
  match SourceSpecializationWorklist.run
      (replaceFunction program wrongBundleFunction)
      [monomorphicRequest apply] 1 with
  | .error (.indirectArgumentBundleMismatch actual .word .bool) =>
      assertTrue (actual == call.id)
        "indirect bundle mismatch lost its call occurrence"
  | result => throw (IO.userError
      s!"indirect metadata detached from argument children was accepted: {reprStr result}")
  let wrongResultFunction : CheckedFunction := {
    function with
    typedBody := {
      function.typedBody with
      nodes := setExpressionType function.typedBody.nodes call.id .bool
    }
  }
  match SourceSpecializationWorklist.run
      (replaceFunction program wrongResultFunction)
      [monomorphicRequest apply] 1 with
  | .error (.indirectResultTypeMismatch actual .word .bool) =>
      assertTrue (actual == call.id)
        "indirect result mismatch lost its call occurrence"
  | result => throw (IO.userError
      s!"indirect result metadata detached from the callee was accepted: {reprStr result}")

private def testIndirectArgumentCountCase (program : CheckedProgram)
    (name : String) (expected forged : Nat) : IO Unit := do
  let signature ← signatureNamed program name
  let function ← functionFor program signature
  let (call, metadata) ← match firstIndirectCall? function.typedBody.nodes with
    | some call => pure call
    | none => throw (IO.userError s!"{name}: indirect call metadata was absent")
  assertTrue (decide (metadata.argumentCount = expected ∧
      metadata.argumentTypeBeforeCoercion = .product .word .bool ∧
      metadata.argumentTypeAfterCoercion = .product .word .bool))
    s!"{name}: product bundle or source argument count was not retained"
  let plan ← match ← runOrThrow name program
      [monomorphicRequest signature] 1 with
    | .complete plan => pure plan
    | outcome => throw (IO.userError
        s!"{name}: expected a complete plan, found {reprStr outcome}")
  let forgedMetadata := { metadata with argumentCount := forged }
  let malformedFunction : CheckedFunction := {
    function with
    typedBody := {
      function.typedBody with
      nodes := setIndirectMetadata function.typedBody.nodes call.id
        forgedMetadata
    }
  }
  let malformedProgram := replaceFunction program malformedFunction
  match SourceSpecializationWorklist.run malformedProgram
      [monomorphicRequest signature] 1 with
  | .error (.indirectArgumentCountMismatch actual retained children) =>
      assertTrue (actual == call.id && retained == forged && children == expected)
        s!"{name}: worklist arity rejection lost its occurrence or counts"
  | result => throw (IO.userError
      s!"{name}: worklist accepted product-bundle arity tampering: {reprStr result}")
  let malformedPlan : SourceSpecializationWorklist.Plan := {
    plan with
    specializations := plan.specializations.map fun specialized =>
      if specialized.declaration == signature.id then
        { specialized with
          function := {
            specialized.function with
            typedBody := {
              specialized.function.typedBody with
              nodes := setIndirectMetadata
                specialized.function.typedBody.nodes call.id forgedMetadata
            }
          }
        }
      else
        specialized
  }
  match SourceRuntimeLinking.link malformedProgram (.complete malformedPlan) with
  | .error (.invalidPlan (.worklist
      (.indirectArgumentCountMismatch actual retained children))) =>
      assertTrue (actual == call.id && retained == forged && children == expected)
        s!"{name}: runtime-link rejection lost its occurrence or counts"
  | result => throw (IO.userError
      s!"{name}: runtime linker accepted product-bundle arity tampering: {reprStr result}")

private def testIndirectArgumentCounts (program : CheckedProgram) : IO Unit := do
  testIndirectArgumentCountCase program "applyProduct" 1 2
  testIndirectArgumentCountCase program "applySplit" 2 1

private def testMalformedTypedMetadata (program : CheckedProgram) : IO Unit := do
  let select ← signatureNamed program "select"
  let function ← functionFor program select
  let (call, callee) ← match firstDirectCall? function.typedBody.nodes with
    | some edge => pure edge
    | none => throw (IO.userError "select: direct call metadata was absent")
  let wrongTypeFunction : CheckedFunction := {
    function with
    typedBody := {
      function.typedBody with
      nodes := setExpressionType function.typedBody.nodes callee .bool
    }
  }
  match SourceSpecializationWorklist.run
      (replaceFunction program wrongTypeFunction)
      [monomorphicRequest select] 2 with
  | .error (.calleeNodeTypeMismatch actualCall .bool _) =>
      assertTrue (actualCall == call)
        "callee-node type mismatch lost the owning call occurrence"
  | result => throw (IO.userError
      s!"malformed callee-node type was not isolated: {reprStr result}")
  let invalidPath : CheckedFunction := {
    function with
    typedBody := {
      function.typedBody with
      nodes := setExpressionCoercions function.typedBody.nodes call [{
        requirement := ⟨99⟩
        source := .word
        target := .bool
      }]
    }
  }
  match SourceSpecializationWorklist.run
      (replaceFunction program invalidPath)
      [monomorphicRequest select] 2 with
  | .error (.invalidExpressionCoercionPath actual .word .word [_]) =>
      assertTrue (actual == call)
        "invalid output coercion path lost its expression occurrence"
  | result => throw (IO.userError
      s!"an output coercion not ending at node.type was accepted: {reprStr result}")
  let wrongParameterComptime : CheckedFunction := {
    function with
    typedBody := {
      function.typedBody with
      nodes := setDirectInstantiationMarkers function.typedBody.nodes
        call callee [true, false] false
    }
  }
  match SourceSpecializationWorklist.run
      (replaceFunction program wrongParameterComptime)
      [monomorphicRequest select] 2 with
  | .error (.specializedCalleeParameterComptimeMismatch
      actual [true, false] [false, false]) =>
      assertTrue (actual == call)
        "callee parameter-marker mismatch lost the owning call occurrence"
  | result => throw (IO.userError
      s!"tampered callee parameter markers were not rejected: {reprStr result}")
  let wrongReturnComptime : CheckedFunction := {
    function with
    typedBody := {
      function.typedBody with
      nodes := setDirectInstantiationMarkers function.typedBody.nodes
        call callee [false, false] true
    }
  }
  match SourceSpecializationWorklist.run
      (replaceFunction program wrongReturnComptime)
      [monomorphicRequest select] 2 with
  | .error (.specializedCalleeReturnComptimeMismatch actual true false) =>
      assertTrue (actual == call)
        "callee result-marker mismatch lost the owning call occurrence"
  | result => throw (IO.userError
      s!"tampered callee result marker was not rejected: {reprStr result}")
  let missingNodeFunction : CheckedFunction := {
    function with
    typedBody := {
      function.typedBody with
      nodes := eraseExpression function.typedBody.nodes callee
    }
  }
  match SourceSpecializationWorklist.run
      (replaceFunction program missingNodeFunction)
      [monomorphicRequest select] 2 with
  | .error (.specialization declaration
      (.stageAnalysis (.missingNode actualCallee))) =>
      assertTrue (declaration == select.id && actualCallee == callee.occurrence)
        "stage-analysis missing-node error lost its declaration or callee identity"
  | result => throw (IO.userError
      s!"missing callee node was not rejected: {reprStr result}")
  let missingDeclarationProgram : CheckedProgram := {
    program with
    environment := {
      program.environment with
      declarations := program.environment.declarations.filter fun declaration =>
        declaration.id != select.id
    }
  }
  match SourceSpecializationWorklist.run missingDeclarationProgram
      [monomorphicRequest select] 2 with
  | .error (.missingDeclaration declaration) =>
      assertTrue (declaration == select.id)
        "missing-declaration error reported the wrong catalog identity"
  | result => throw (IO.userError
      s!"missing environment declaration was not rejected: {reprStr result}")

/-- Exercise canonical FIFO discovery, per-occurrence direct and function-value
edges, recursion deduplication, finite type-growing recursion, retained
assumptions/evidence, malformed catalog/metadata rejection, and indirect-call
validation from one checked raw workspace. -/
def testSourceSpecializationWorklist : IO Unit := do
  let program ← checkedProgram
  testBreadthFirstDiscovery program
  testDerivedCanonicalization program
  testTypedNodeOrder program
  testRecursiveKeys program
  testAssumptionPreservation program
  testFunctionValueReference program
  testIndirectCallBoundary program
  testIndirectArgumentCounts program
  testMalformedTypedMetadata program

end Tests.SourceSpecializationWorklist
