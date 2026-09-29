import Solcore.Frontend.SourceRuntimeLinking
import Solcore.Frontend.SourceTypedRuntime

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
      "impl Eq<Bool> {}",
      "function identity<T>(value: T) returns (T) { return value; }",
      "function globalIdentity<T>(value: T) returns (T) { return value; }",
      "function choose3<A, B, C>(first: A, second: B, third: C) returns (C) { return third; }",
      "function twice<T>(value: T) returns (T) { return identity(identity(value)); }",
      "function contextualLocal(flag: Bool) returns (Word, Bool) {",
      "  let f = lam(value) { return identity(value); };",
      "  f(2);",
      "  return (f(1), f(flag));",
      "}",
      "function unusedContextualLocal() returns (Word) {",
      "  let f = lam(value) { return identity(value); };",
      "  return 9;",
      "}",
      "function nestedContextualLocal(flag: Bool) returns (Word, Bool) {",
      "  let outer = lam(value) {",
      "    let inner = lam(nestedValue) { return identity(nestedValue); };",
      "    return inner(value);",
      "  };",
      "  return (outer(1), outer(flag));",
      "}",
      "function groundInnerUnderPolymorphicOuter(flag: Bool) returns (Word, Word) {",
      "  let outer = lam(value) {",
      "    let inner = lam(item) { return globalIdentity(item); };",
      "    return inner(1);",
      "  };",
      "  return (outer(1), outer(flag));",
      "}",
      "function siblingContextualLocal(flag: Bool) returns (Word, Bool) {",
      "  let outer = lam(value) {",
      "    let left = lam(item) { return identity(item); };",
      "    let right = lam(item) { return identity(item); };",
      "    left(value);",
      "    return right(value);",
      "  };",
      "  return (outer(1), outer(flag));",
      "}",
      "function depthThreeContextualLocal(flag: Bool) returns (Word, Bool) {",
      "  let outer = lam(value) {",
      "    let middle = lam(item) {",
      "      let inner = lam(nestedValue) { return identity(nestedValue); };",
      "      return inner(item);",
      "    };",
      "    return middle(value);",
      "  };",
      "  return (outer(1), outer(flag));",
      "}",
      "function scopeAwareRecursiveContextualLocal(flag: Bool) returns (Word, Bool) {",
      "  let outer = lam(value) {",
      "    let middle = lam(item) {",
      "      let inner = lam(nestedValue) {",
      "        return choose3(value, item, nestedValue);",
      "      };",
      "      return inner(value);",
      "    };",
      "    return middle(value);",
      "  };",
      "  return (outer(1), outer(flag));",
      "}",
      "function mixedScopeDepthThreeContextualLocal(flag: Bool) returns (Word) {",
      "  let outer = lam(value) {",
      "    let middle = lam(item) {",
      "      let inner = lam(pair) { return identity(pair); };",
      "      return inner((value, item));",
      "    };",
      "    return middle(value);",
      "  };",
      "  outer(1);",
      "  outer(flag);",
      "  return 9;",
      "}",
      "function reusedBinderMixedScopeContextualLocal(flag: Bool) returns (Word) {",
      "  let outer = lam(value) {",
      "    let adapter = lam(item) { return identity(item); };",
      "    adapter(value);",
      "    let middle = lam(item) { return adapter((value, item)); };",
      "    return middle(value);",
      "  };",
      "  outer(1);",
      "  outer(flag);",
      "  return 9;",
      "}",
      "function monomorphicLambdaWrapper() returns (Word) {",
      "  let outer = lam() {",
      "    let f = lam(item) { return identity(item); };",
      "    return f(1);",
      "  };",
      "  return outer();",
      "}",
      "function unusedNestedContextualLocal() returns (Word) {",
      "  let outer = lam(value) {",
      "    let inner = lam(item) { return identity(item); };",
      "    return inner(value);",
      "  };",
      "  return 9;",
      "}",
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
      "function qualifiedLocal(flag: Bool) returns (Word, Bool) {",
      "  let f = lam(value) { return keep(value); };",
      "  return (f(1), f(flag));",
      "}",
      "function constrained(value: Word) returns (Word) { return keep(value); }",
      "function keepAs<T, U>(guard: T, value: U) returns (U) where T: Eq { return value; }",
      "function localProof(flag: Bool) returns (Word, Bool) {",
      "  let f = lam(value) { return keepAs(1, value); };",
      "  return (f(2), f(flag));",
      "}",
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

private def traitNamed (program : CheckedProgram) (name : String) :
    IO ProgramTraitSignature := do
  match program.signatures.traits.filter fun signature =>
      signature.name == name with
  | [signature] => pure signature
  | signatures => throw (IO.userError
      s!"expected one trait named `{name}`, found {signatures.length}")

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

private def setLocalBinderScheme (nodes : List Node)
    (target : Resolved.LocalId) (scheme : Scheme) : List Node :=
  nodes.map fun node => match node with
  | .statement statement =>
      match statement.form with
      | .letDecl binder initializer =>
          if binder.id == target then
            .statement {
              statement with
              form := .letDecl { binder with scheme } initializer
            }
          else
            node
      | _ => node
  | .expression _ => node

private def setLocalBinderRequirements (nodes : List Node)
    (target : Resolved.LocalId)
    (requirements : List LocalSchemeRequirement) : List Node :=
  nodes.map fun node => match node with
  | .statement statement =>
      match statement.form with
      | .letDecl binder initializer =>
          if binder.id == target then
            .statement {
              statement with
              form := .letDecl { binder with schemeRequirements := requirements }
                initializer
            }
          else
            node
      | _ => node
  | .expression _ => node

private def setExpressionRequirements (nodes : List Node)
    (target : ExpressionId) (requirements : List RequirementId) : List Node :=
  nodes.map fun node => match node with
  | .expression expression =>
      if expression.id == target then
        .expression { expression with requirements }
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

private def testContextualLocalPolymorphicCalls
    (program : CheckedProgram) : IO Unit := do
  let identity ← signatureNamed program "identity"
  let contextual ← signatureNamed program "contextualLocal"
  let function ← functionFor program contextual
  let (binder, initializer) ← match function.typedBody.nodes.filterMap fun
      | .statement { form := .letDecl binder (some initializer), .. } =>
          if binder.name == "f" then some (binder, initializer) else none
      | _ => none with
    | [(binder, initializer)] => pure (binder, initializer)
    | bindings => throw (IO.userError
        s!"contextualLocal retained {bindings.length} binders named `f`")
  let quantified ← match binder.scheme.quantified with
    | [quantified] => pure quantified
    | variables => throw (IO.userError
        s!"contextualLocal `f` retained {variables.length} quantified variables")
  let declarationParameter ← match identity.scheme.parameters with
    | [parameter] => pure parameter
    | parameters => throw (IO.userError
        s!"identity retained {parameters.length} declaration parameters")
  let (call, callee, callInstantiation) ← match
      function.typedBody.nodes.findSome? fun
        | .expression node@{
            form := .call callee _ (.declaration instantiation), .. } =>
            if instantiation.declaration == identity.id then
              some (node, callee, instantiation)
            else
              none
        | _ => none with
    | some selected => pure selected
    | none => throw (IO.userError
        "contextualLocal lost its declaration call to identity")
  let calleeNode ← match function.typedBody.lookupExpression? callee with
    | some node@{ form := .reference _ (.declaration _), .. } => pure node
    | _ => throw (IO.userError
        "contextualLocal identity call lost its declaration-reference child")
  let localReferenceTypes := function.typedBody.nodes.filterMap fun
    | .expression node@{ form := .reference _ (.local selected), .. } =>
        if selected == binder.id then some node.rawType else none
    | _ => none
  let residual := Ty.variable quantified
  assertTrue (SourceSpecialization.isDirectLambdaInitializer
      function.typedBody initializer && decide (
        binder.scheme.body = .function residual residual ∧
        call.rawType = residual ∧ call.type = residual ∧
        callInstantiation.parameterSubstitution =
          [(declarationParameter, residual)] ∧
        callInstantiation.type = .function residual residual ∧
        callInstantiation.predicates = [] ∧
        calleeNode.rawType = .function residual residual ∧
        localReferenceTypes = [
          Ty.function .word .word,
          Ty.function .word .word,
          Ty.function .bool .bool]))
    "contextualLocal did not retain its principal template and three concrete uses"

  let entryKey : SourceSpecialization.SpecializationKey := {
    declaration := contextual.id
    arguments := []
  }
  let wordKey : SourceSpecialization.SpecializationKey := {
    declaration := identity.id
    arguments := [.word]
  }
  let boolKey : SourceSpecialization.SpecializationKey := {
    declaration := identity.id
    arguments := [.bool]
  }
  let request := monomorphicRequest contextual
  match ← runOrThrow "contextual local calls" program [request] 3 with
  | .complete plan =>
      let expectedEdges : List SourceSpecializationWorklist.CallEdge := [{
        caller := entryKey
        occurrence := call.id
        callee := wordKey
      }, {
        caller := entryKey
        occurrence := call.id
        callee := boolKey
      }]
      assertTrue (decide (
          plan.seedKeys = [entryKey] ∧
          plan.specializations.map (·.key) = [entryKey, wordKey, boolKey] ∧
          plan.callEdges = expectedEdges ∧
          plan.callEdges.eraseDups.length = 2 ∧
          plan.referenceEdges = []))
        "contextual local calls lost canonical keys or exact deduplicated edges"
      match SourceCoreDirectLinking.validatePlan program plan with
      | .ok () => pure ()
      | .error error => throw (IO.userError
          s!"contextual local plan failed replay validation: {reprStr error}")
  | outcome => throw (IO.userError
      s!"contextual local calls: expected a complete plan, found {reprStr outcome}")

  match ← runOrThrow "contextual local budget one" program [request] 1 with
  | .budgetExhausted plan next pending =>
      assertTrue (decide (
          plan.specializations.map (·.key) = [entryKey] ∧
          plan.callEdges.length = 2 ∧
          plan.callEdges.map (·.occurrence) = [call.id, call.id] ∧
          next = wordKey ∧ pending.length = 2))
        "contextual local budget one lost its concrete frontier or edge ledger"
  | outcome => throw (IO.userError
      s!"contextual local budget one: expected exhaustion, found {reprStr outcome}")

  match ← runOrThrow "contextual local budget two" program [request] 2 with
  | .budgetExhausted plan next pending =>
      assertTrue (decide (
          plan.specializations.map (·.key) = [entryKey, wordKey] ∧
          plan.callEdges.length = 2 ∧ next = boolKey ∧
          pending.length = 1))
        "contextual local budget two lost its second concrete frontier"
  | outcome => throw (IO.userError
      s!"contextual local budget two: expected exhaustion, found {reprStr outcome}")

  let unused ← signatureNamed program "unusedContextualLocal"
  match ← runOrThrow "unused contextual local" program
      [monomorphicRequest unused] 1 with
  | .complete plan =>
      assertTrue (decide (plan.specializations.map (·.key.declaration) =
          [unused.id] ∧ plan.callEdges = [] ∧ plan.referenceEdges = []))
        "an unused polymorphic lambda unnecessarily specialized its open body"
  | outcome => throw (IO.userError
      s!"unused contextual local: expected a complete plan, found {reprStr outcome}")

  let wordReference ← match function.typedBody.nodes.findSome? fun
      | .expression node@{ form := .reference _ (.local selected), .. } =>
          if selected == binder.id &&
              node.rawType == Ty.function .word .word then
            some node
          else
            none
      | _ => none with
    | some reference => pure reference
    | none => throw (IO.userError
        "contextualLocal lost its concrete Word reference to `f`")
  let mismatchedScheme : Scheme := {
    binder.scheme with body := .function residual .bool
  }
  let mismatchedFunction : CheckedFunction := {
    function with
    typedBody := {
      function.typedBody with
      nodes := setLocalBinderScheme function.typedBody.nodes
        binder.id mismatchedScheme
    }
  }
  match SourceSpecializationWorklist.run
      (replaceFunction program mismatchedFunction) [request] 3 with
  | .error (.localPolymorphicInstanceMismatch occurrence binderId scheme
      (.function .word .word)) =>
      assertTrue (decide (occurrence = wordReference.id ∧ binderId = binder.id ∧
          scheme = mismatchedScheme))
        "local scheme-instance mismatch lost its occurrence or binder"
  | result => throw (IO.userError
      s!"a malformed ground local scheme instance was accepted: {reprStr result}")

private def testDepthTwoContextualLocalPolymorphicCalls
    (program : CheckedProgram) : IO Unit := do
  let identity ← signatureNamed program "identity"
  let nested ← signatureNamed program "nestedContextualLocal"
  let function ← functionFor program nested
  let call ← match function.typedBody.nodes.findSome? fun
      | .expression node@{
          form := .call _ _ (.declaration instantiation), .. } =>
          if instantiation.declaration == identity.id then some node else none
      | _ => none with
    | some call => pure call
    | none => throw (IO.userError
        "nestedContextualLocal lost its declaration call to identity")
  let entryKey : SourceSpecialization.SpecializationKey := {
    declaration := nested.id
    arguments := []
  }
  let wordKey : SourceSpecialization.SpecializationKey := {
    declaration := identity.id
    arguments := [.word]
  }
  let boolKey : SourceSpecialization.SpecializationKey := {
    declaration := identity.id
    arguments := [.bool]
  }
  let expectedEdges : List SourceSpecializationWorklist.CallEdge := [{
    caller := entryKey
    occurrence := call.id
    callee := wordKey
  }, {
    caller := entryKey
    occurrence := call.id
    callee := boolKey
  }]
  let request := monomorphicRequest nested

  match ← runOrThrow "depth-two contextual local calls" program
      [request] 3 with
  | .complete plan =>
      assertTrue (decide (
          plan.seedKeys = [entryKey] ∧
          plan.specializations.map (·.key) = [entryKey, wordKey, boolKey] ∧
          plan.callEdges = expectedEdges ∧
          plan.callEdges.eraseDups.length = 2 ∧
          plan.callEdges.map (·.occurrence) = [call.id, call.id] ∧
          plan.referenceEdges = []))
        "depth-two local calls lost canonical keys or exact deduplicated edges"
      match SourceCoreDirectLinking.validatePlan program plan with
      | .ok () => pure ()
      | .error error => throw (IO.userError
          s!"depth-two local plan failed replay validation: {reprStr error}")
  | outcome => throw (IO.userError
      s!"depth-two local calls: expected a complete plan, found {reprStr outcome}")

  match ← runOrThrow "depth-two contextual budget one" program
      [request] 1 with
  | .budgetExhausted plan next pending =>
      assertTrue (decide (
          plan.specializations.map (·.key) = [entryKey] ∧
          plan.callEdges = expectedEdges ∧ next = wordKey ∧
          pending.length = 2))
        "depth-two budget one lost its concrete frontier or edge ledger"
  | outcome => throw (IO.userError
      s!"depth-two budget one: expected exhaustion, found {reprStr outcome}")

  match ← runOrThrow "depth-two contextual budget two" program
      [request] 2 with
  | .budgetExhausted plan next pending =>
      assertTrue (decide (
          plan.specializations.map (·.key) = [entryKey, wordKey] ∧
          plan.callEdges = expectedEdges ∧ next = boolKey ∧
          pending.length = 1))
        "depth-two budget two lost its second concrete frontier"
  | outcome => throw (IO.userError
      s!"depth-two budget two: expected exhaustion, found {reprStr outcome}")

private def testGroundInnerUnderPolymorphicOuter
    (program : CheckedProgram) : IO Unit := do
  let identity ← signatureNamed program "globalIdentity"
  let entry ← signatureNamed program "groundInnerUnderPolymorphicOuter"
  let function ← functionFor program entry
  let outer ← match function.typedBody.nodes.findSome? fun
      | .statement { form := .letDecl binder (some _), .. } =>
          if binder.name == "outer" then some binder else none
      | _ => none with
    | some binder => pure binder
    | none => throw (IO.userError
        "ground-inner fixture lost its `outer` binder")
  let inner ← match function.typedBody.nodes.findSome? fun
      | .statement { form := .letDecl binder (some _), .. } =>
          if binder.name == "inner" then some binder else none
      | _ => none with
    | some binder => pure binder
    | none => throw (IO.userError
        "ground-inner fixture lost its `inner` binder")
  let quantified ← match inner.scheme.quantified with
    | [quantified] => pure quantified
    | variables => throw (IO.userError
        s!"ground-inner `inner` retained {variables.length} quantified variables")
  let declarationParameter ← match identity.scheme.parameters with
    | [parameter] => pure parameter
    | parameters => throw (IO.userError
        s!"globalIdentity retained {parameters.length} parameters")
  let innerReference ← match function.typedBody.nodes.filterMap fun
      | .expression node@{ form := .reference _ (.local selected), .. } =>
          if selected == inner.id then some node else none
      | _ => none with
    | [reference] => pure reference
    | references => throw (IO.userError
        s!"ground-inner fixture retained {references.length} inner references")
  let (call, instantiation) ← match
      function.typedBody.nodes.findSome? fun
        | .expression node@{
            form := .call _ _ (.declaration instantiation), .. } =>
            if instantiation.declaration == identity.id then
              some (node, instantiation)
            else
              none
        | _ => none with
    | some selected => pure selected
    | none => throw (IO.userError
        "ground-inner fixture lost its globalIdentity call")
  let residual := Ty.variable quantified
  assertTrue (decide (
      outer.scheme.quantified.length = 1 ∧
      inner.scheme.body = .function residual residual ∧
      innerReference.rawType = .function .word .word ∧
      instantiation.parameterSubstitution = [(declarationParameter, residual)] ∧
      instantiation.type = .function residual residual))
    "ground-inner fixture lost its ground use or open helper metadata"

  let entryKey : SourceSpecialization.SpecializationKey := {
    declaration := entry.id
    arguments := []
  }
  let wordKey : SourceSpecialization.SpecializationKey := {
    declaration := identity.id
    arguments := [.word]
  }
  let expectedEdge : SourceSpecializationWorklist.CallEdge := {
    caller := entryKey
    occurrence := call.id
    callee := wordKey
  }
  match ← runOrThrow "ground inner under polymorphic outer" program
      [monomorphicRequest entry] 2 with
  | .complete plan =>
      assertTrue (decide (
          plan.seedKeys = [entryKey] ∧
          plan.specializations.map (·.key) = [entryKey, wordKey] ∧
          plan.callEdges = [expectedEdge] ∧
          plan.callEdges.eraseDups.length = 1 ∧
          plan.referenceEdges = []))
        "ground inner use was duplicated or lost across outer contexts"
      match SourceCoreDirectLinking.validatePlan program plan with
      | .error error => throw (IO.userError
          s!"ground-inner plan failed replay validation: {reprStr error}")
      | .ok () =>
          match SourceTypedRuntime.run program plan entryKey
              [.bool true] 4096 with
          | .done (.product (.word left) (.word right)) _ =>
              let expected := Core.Word.ofNatModulo 1
              assertTrue (left == expected && right == expected)
                "ground-inner runtime returned the wrong Word pair"
          | result => throw (IO.userError
              s!"ground-inner runtime returned {reprStr result}")
  | outcome => throw (IO.userError
      s!"ground-inner worklist expected a complete plan, found {reprStr outcome}")

private def testSiblingContextualLocalPolymorphicCalls
    (program : CheckedProgram) : IO Unit := do
  let identity ← signatureNamed program "identity"
  let siblings ← signatureNamed program "siblingContextualLocal"
  let function ← functionFor program siblings
  let calls := function.typedBody.nodes.filterMap fun
    | .expression node@{
        form := .call _ _ (.declaration instantiation), .. } =>
        if instantiation.declaration == identity.id then some node else none
    | _ => none
  let (leftCall, rightCall) ← match calls with
    | [leftCall, rightCall] => pure (leftCall, rightCall)
    | calls => throw (IO.userError
        s!"siblingContextualLocal retained {calls.length} identity calls")
  let entryKey : SourceSpecialization.SpecializationKey := {
    declaration := siblings.id
    arguments := []
  }
  let wordKey : SourceSpecialization.SpecializationKey := {
    declaration := identity.id
    arguments := [.word]
  }
  let boolKey : SourceSpecialization.SpecializationKey := {
    declaration := identity.id
    arguments := [.bool]
  }
  let expectedEdges : List SourceSpecializationWorklist.CallEdge := [
    { caller := entryKey, occurrence := leftCall.id, callee := wordKey },
    { caller := entryKey, occurrence := leftCall.id, callee := boolKey },
    { caller := entryKey, occurrence := rightCall.id, callee := wordKey },
    { caller := entryKey, occurrence := rightCall.id, callee := boolKey }
  ]
  match ← runOrThrow "sibling contextual local calls" program
      [monomorphicRequest siblings] 3 with
  | .complete plan =>
      let exactEdges :=
        plan.callEdges.length == expectedEdges.length &&
        plan.callEdges.eraseDups.length == expectedEdges.length &&
        plan.callEdges.all expectedEdges.contains &&
        expectedEdges.all plan.callEdges.contains
      assertTrue (decide (
          plan.seedKeys = [entryKey] ∧
          plan.specializations.map (·.key) = [entryKey, wordKey, boolKey] ∧
          plan.referenceEdges = []) && exactEdges)
        "sibling contexts lost a concrete key or one of four exact call edges"
      match SourceCoreDirectLinking.validatePlan program plan with
      | .ok () => pure ()
      | .error error => throw (IO.userError
          s!"sibling contextual plan failed replay validation: {reprStr error}")
  | outcome => throw (IO.userError
      s!"sibling contextual calls: expected a complete plan, found {reprStr outcome}")

private def testDepthThreeContextualLocalPolymorphicCalls
    (program : CheckedProgram) : IO Unit := do
  let identity ← signatureNamed program "identity"
  let nested ← signatureNamed program "depthThreeContextualLocal"
  let function ← functionFor program nested
  let call ← match function.typedBody.nodes.findSome? fun
      | .expression node@{
          form := .call _ _ (.declaration instantiation), .. } =>
          if instantiation.declaration == identity.id then some node else none
      | _ => none with
    | some call => pure call
    | none => throw (IO.userError
        "depth-three fixture lost its declaration call to identity")
  let entryKey : SourceSpecialization.SpecializationKey := {
    declaration := nested.id
    arguments := []
  }
  let wordKey : SourceSpecialization.SpecializationKey := {
    declaration := identity.id
    arguments := [.word]
  }
  let boolKey : SourceSpecialization.SpecializationKey := {
    declaration := identity.id
    arguments := [.bool]
  }
  let expectedEdges : List SourceSpecializationWorklist.CallEdge := [
    { caller := entryKey, occurrence := call.id, callee := wordKey },
    { caller := entryKey, occurrence := call.id, callee := boolKey }
  ]
  match ← runOrThrow "depth-three contextual local calls" program
      [monomorphicRequest nested] 3 with
  | .complete plan =>
      assertTrue (decide (
          plan.seedKeys = [entryKey] ∧
          plan.specializations.map (·.key) = [entryKey, wordKey, boolKey] ∧
          plan.callEdges = expectedEdges ∧
          plan.callEdges.eraseDups.length = 2 ∧
          plan.referenceEdges = []))
        "depth-three recursion lost its Word/Bool identity instances"
      match SourceCoreDirectLinking.validatePlan program plan with
      | .ok () => pure ()
      | .error error => throw (IO.userError
          s!"depth-three contextual plan failed replay validation: {reprStr error}")
  | outcome => throw (IO.userError
      s!"depth-three contextual calls: expected complete, found {reprStr outcome}")

private def testScopeAwareRecursiveContextualLocalPolymorphicCalls
    (program : CheckedProgram) : IO Unit := do
  let choose3 ← signatureNamed program "choose3"
  let nested ← signatureNamed program "scopeAwareRecursiveContextualLocal"
  let function ← functionFor program nested
  let inner ← match function.typedBody.nodes.findSome? fun
      | .statement { form := .letDecl binder (some _), .. } =>
          if binder.name == "inner" then some binder else none
      | _ => none with
    | some binder => pure binder
    | none => throw (IO.userError
        "scope-aware fixture lost its `inner` binder")
  let innerReference ← match function.typedBody.nodes.findSome? fun
      | .expression node@{ form := .reference _ (.local selected), .. } =>
          if selected == inner.id then some node else none
      | _ => none with
    | some reference => pure reference
    | none => throw (IO.userError
        "scope-aware fixture lost its `inner` reference")
  let (call, instantiation) ← match
      function.typedBody.nodes.findSome? fun
        | .expression node@{
            form := .call _ _ (.declaration instantiation), .. } =>
            if instantiation.declaration == choose3.id then
              some (node, instantiation)
            else
              none
        | _ => none with
    | some selected => pure selected
    | none => throw (IO.userError
        "scope-aware fixture lost its declaration call to choose3")
  let metadataVariables :=
    (instantiation.parameterSubstitution.flatMap fun entry =>
      entry.2.freeVariables).eraseDups
  assertTrue (decide (
      innerReference.rawType.freeVariables.length = 1 ∧
      metadataVariables.length = 3))
    "scope-aware fixture did not separate its reference type from helper metadata"
  let entryKey : SourceSpecialization.SpecializationKey := {
    declaration := nested.id
    arguments := []
  }
  let wordKey : SourceSpecialization.SpecializationKey := {
    declaration := choose3.id
    arguments := [.word, .word, .word]
  }
  let boolKey : SourceSpecialization.SpecializationKey := {
    declaration := choose3.id
    arguments := [.bool, .bool, .bool]
  }
  let expectedEdges : List SourceSpecializationWorklist.CallEdge := [
    { caller := entryKey, occurrence := call.id, callee := wordKey },
    { caller := entryKey, occurrence := call.id, callee := boolKey }
  ]
  match ← runOrThrow "scope-aware recursive contextual calls" program
      [monomorphicRequest nested] 3 with
  | .complete plan =>
      assertTrue (decide (
          plan.seedKeys = [entryKey] ∧
          plan.specializations.map (·.key) = [entryKey, wordKey, boolKey] ∧
          plan.callEdges = expectedEdges ∧
          plan.callEdges.eraseDups.length = 2 ∧
          plan.referenceEdges = []))
        "scope-aware recursion lost its triple-ground helper instances"
      match SourceCoreDirectLinking.validatePlan program plan with
      | .ok () => pure ()
      | .error error => throw (IO.userError
          s!"scope-aware contextual plan failed replay validation: {reprStr error}")
  | outcome => throw (IO.userError
      s!"scope-aware calls: expected a complete plan, found {reprStr outcome}")

private def testMixedScopeDepthThreeContextualLocalPolymorphicCalls
    (program : CheckedProgram) : IO Unit := do
  let identity ← signatureNamed program "identity"
  let nested ← signatureNamed program "mixedScopeDepthThreeContextualLocal"
  let function ← functionFor program nested
  let inner ← match function.typedBody.nodes.findSome? fun
      | .statement { form := .letDecl binder (some _), .. } =>
          if binder.name == "inner" then some binder else none
      | _ => none with
    | some binder => pure binder
    | none => throw (IO.userError
        "mixed-scope depth-three fixture lost its `inner` binder")
  let openReference ← match function.typedBody.nodes.findSome? fun
      | .expression node@{ form := .reference _ (.local selected), .. } =>
          if selected == inner.id && node.rawType.freeVariables.length == 2 then
            some node
          else
            none
      | _ => none with
    | some reference => pure reference
    | none => throw (IO.userError
        "mixed-scope depth-three fixture lost its two-variable inner reference")
  let expectedVariables := openReference.rawType.freeVariables
  assertTrue (expectedVariables.length == 2)
    "mixed-scope inner reference did not retain outer and middle variables"
  let call ← match function.typedBody.nodes.findSome? fun
      | .expression node@{
          form := .call _ _ (.declaration instantiation), .. } =>
          if instantiation.declaration == identity.id then some node else none
      | _ => none with
    | some call => pure call
    | none => throw (IO.userError
        "mixed-scope depth-three fixture lost its identity call")
  let entryKey : SourceSpecialization.SpecializationKey := {
    declaration := nested.id
    arguments := []
  }
  let wordProduct := Ty.product .word .word
  let boolProduct := Ty.product .bool .bool
  let wordKey : SourceSpecialization.SpecializationKey := {
    declaration := identity.id
    arguments := [wordProduct]
  }
  let boolKey : SourceSpecialization.SpecializationKey := {
    declaration := identity.id
    arguments := [boolProduct]
  }
  let expectedEdges : List SourceSpecializationWorklist.CallEdge := [
    { caller := entryKey, occurrence := call.id, callee := wordKey },
    { caller := entryKey, occurrence := call.id, callee := boolKey }
  ]
  match ← runOrThrow "mixed-scope depth-three calls" program
      [monomorphicRequest nested] 3 with
  | .complete plan =>
      assertTrue (decide (
          plan.seedKeys = [entryKey] ∧
          plan.specializations.map (·.key) = [entryKey, wordKey, boolKey] ∧
          plan.callEdges = expectedEdges ∧
          plan.callEdges.eraseDups.length = 2 ∧
          plan.referenceEdges = []))
        "mixed-scope recursion lost its product identity instances"
      match SourceCoreDirectLinking.validatePlan program plan with
      | .ok () => pure ()
      | .error error => throw (IO.userError
          s!"mixed-scope contextual plan failed replay validation: {reprStr error}")
  | outcome => throw (IO.userError
      s!"mixed-scope calls: expected a complete plan, found {reprStr outcome}")

private def testReusedBinderMixedScopeContextualLocalPolymorphicCalls
    (program : CheckedProgram) : IO Unit := do
  let identity ← signatureNamed program "identity"
  let nested ← signatureNamed program "reusedBinderMixedScopeContextualLocal"
  let function ← functionFor program nested
  let adapter ← match function.typedBody.nodes.findSome? fun
      | .statement { form := .letDecl binder (some _), .. } =>
          if binder.name == "adapter" then some binder else none
      | _ => none with
    | some binder => pure binder
    | none => throw (IO.userError
        "reused-binder fixture lost its `adapter` binder")
  let adapterReferences := function.typedBody.nodes.filterMap fun
    | .expression node@{ form := .reference _ (.local selected), .. } =>
        if selected == adapter.id then some node else none
    | _ => none
  let directReference ← match adapterReferences.find? fun node =>
      node.rawType.freeVariables.length == 1 with
    | some reference => pure reference
    | none => throw (IO.userError
        "reused-binder fixture lost its direct-child adapter reference")
  let mixedReference ← match adapterReferences.find? fun node =>
      node.rawType.freeVariables.length == 2 with
    | some reference => pure reference
    | none => throw (IO.userError
        "reused-binder fixture lost its mixed-scope adapter reference")
  assertTrue (directReference.id != mixedReference.id)
    "reused-binder fixture collapsed its distinct adapter occurrences"
  assertTrue (mixedReference.rawType.freeVariables.length == 2)
    "reused-binder mixed occurrence lost an enclosing variable"
  let call ← match function.typedBody.nodes.findSome? fun
      | .expression node@{
          form := .call _ _ (.declaration instantiation), .. } =>
          if instantiation.declaration == identity.id then some node else none
      | _ => none with
    | some call => pure call
    | none => throw (IO.userError
        "reused-binder fixture lost its identity call")
  let entryKey : SourceSpecialization.SpecializationKey := {
    declaration := nested.id
    arguments := []
  }
  let wordKey : SourceSpecialization.SpecializationKey := {
    declaration := identity.id
    arguments := [.word]
  }
  let boolKey : SourceSpecialization.SpecializationKey := {
    declaration := identity.id
    arguments := [.bool]
  }
  let wordProductKey : SourceSpecialization.SpecializationKey := {
    declaration := identity.id
    arguments := [.product .word .word]
  }
  let boolProductKey : SourceSpecialization.SpecializationKey := {
    declaration := identity.id
    arguments := [.product .bool .bool]
  }
  let expectedEdges : List SourceSpecializationWorklist.CallEdge := [
    { caller := entryKey, occurrence := call.id, callee := wordKey },
    { caller := entryKey, occurrence := call.id, callee := boolKey },
    { caller := entryKey, occurrence := call.id, callee := wordProductKey },
    { caller := entryKey, occurrence := call.id, callee := boolProductKey }
  ]
  match ← runOrThrow "reused-binder mixed-scope calls" program
      [monomorphicRequest nested] 5 with
  | .complete plan =>
      assertTrue (decide (
          plan.seedKeys = [entryKey] ∧
          plan.specializations.map (·.key) =
            [entryKey, wordKey, boolKey, wordProductKey, boolProductKey] ∧
          plan.callEdges = expectedEdges ∧
          plan.callEdges.eraseDups.length = 4 ∧
          plan.referenceEdges = []))
        "reused binder lost a direct or mixed product identity instance"
      match SourceCoreDirectLinking.validatePlan program plan with
      | .ok () => pure ()
      | .error error => throw (IO.userError
          s!"reused-binder contextual plan failed replay validation: {reprStr error}")
  | outcome => throw (IO.userError
      s!"reused-binder calls: expected a complete plan, found {reprStr outcome}")

private def testMonomorphicLambdaWrapperContextualLocal
    (program : CheckedProgram) : IO Unit := do
  let identity ← signatureNamed program "identity"
  let wrapper ← signatureNamed program "monomorphicLambdaWrapper"
  let function ← functionFor program wrapper
  let outer ← match function.typedBody.nodes.findSome? fun
      | .statement { form := .letDecl binder (some _), .. } =>
          if binder.name == "outer" then some binder else none
      | _ => none with
    | some binder => pure binder
    | none => throw (IO.userError
        "monomorphic-wrapper fixture lost its `outer` binder")
  let inner ← match function.typedBody.nodes.findSome? fun
      | .statement { form := .letDecl binder (some _), .. } =>
          if binder.name == "f" then some binder else none
      | _ => none with
    | some binder => pure binder
    | none => throw (IO.userError
        "monomorphic-wrapper fixture lost its `f` binder")
  assertTrue (outer.scheme.quantified.isEmpty &&
      inner.scheme.quantified.length == 1)
    "monomorphic-wrapper fixture did not retain its intended schemes"
  let call ← match function.typedBody.nodes.findSome? fun
      | .expression node@{
          form := .call _ _ (.declaration instantiation), .. } =>
          if instantiation.declaration == identity.id then some node else none
      | _ => none with
    | some call => pure call
    | none => throw (IO.userError
        "monomorphic-wrapper fixture lost its identity call")
  let entryKey : SourceSpecialization.SpecializationKey := {
    declaration := wrapper.id
    arguments := []
  }
  let wordKey : SourceSpecialization.SpecializationKey := {
    declaration := identity.id
    arguments := [.word]
  }
  let expectedEdge : SourceSpecializationWorklist.CallEdge := {
    caller := entryKey
    occurrence := call.id
    callee := wordKey
  }
  match ← runOrThrow "monomorphic lambda wrapper" program
      [monomorphicRequest wrapper] 2 with
  | .complete plan =>
      assertTrue (decide (
          plan.seedKeys = [entryKey] ∧
          plan.specializations.map (·.key) = [entryKey, wordKey] ∧
          plan.callEdges = [expectedEdge] ∧
          plan.referenceEdges = []))
        "ground local use under a monomorphic lambda wrapper was not discovered"
      match SourceCoreDirectLinking.validatePlan program plan with
      | .ok () => pure ()
      | .error error => throw (IO.userError
          s!"monomorphic-wrapper plan failed replay validation: {reprStr error}")
  | outcome => throw (IO.userError
      s!"monomorphic wrapper: expected a complete plan, found {reprStr outcome}")

private def testUnusedNestedContextualLocal
    (program : CheckedProgram) : IO Unit := do
  let unused ← signatureNamed program "unusedNestedContextualLocal"
  let entryKey : SourceSpecialization.SpecializationKey := {
    declaration := unused.id
    arguments := []
  }
  match ← runOrThrow "unused nested contextual local" program
      [monomorphicRequest unused] 1 with
  | .complete plan =>
      assertTrue (decide (
          plan.seedKeys = [entryKey] ∧
          plan.specializations.map (·.key) = [entryKey] ∧
          plan.callEdges = [] ∧ plan.referenceEdges = []))
        "an unreachable nested polymorphic template was scanned or rejected"
      match SourceCoreDirectLinking.validatePlan program plan with
      | .ok () => pure ()
      | .error error => throw (IO.userError
          s!"unused nested local plan failed replay validation: {reprStr error}")
  | outcome => throw (IO.userError
      s!"unused nested local: expected a complete plan, found {reprStr outcome}")

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

private def testContextualLocalProofCalls
    (program : CheckedProgram) : IO Unit := do
  let eq ← traitNamed program "Eq"
  let keepAs ← signatureNamed program "keepAs"
  let localProof ← signatureNamed program "localProof"
  let function ← functionFor program localProof
  let (call, instantiation) ← match
      function.typedBody.nodes.findSome? fun
        | .expression node@{
            form := .call _ _ (.declaration instantiation), .. } =>
            if instantiation.declaration == keepAs.id then
              some (node, instantiation)
            else
              none
        | _ => none with
    | some selected => pure selected
    | none => throw (IO.userError
        "localProof lost its declaration call to keepAs")
  let requirement ← match call.requirements with
    | [requirement] => pure requirement
    | requirements => throw (IO.userError
        s!"localProof keepAs call retained {requirements.length} requirements")
  let predicate : ProgramPredicate := {
    trait := eq.id
    subject := .word
    arguments := []
  }
  assertTrue (decide (instantiation.predicates = [predicate]))
    "localProof keepAs metadata lost its ground Eq<Word> predicate"

  let entryKey : SourceSpecialization.SpecializationKey := {
    declaration := localProof.id
    arguments := []
  }
  let wordKey : SourceSpecialization.SpecializationKey := {
    declaration := keepAs.id
    arguments := [.word, .word]
  }
  let boolKey : SourceSpecialization.SpecializationKey := {
    declaration := keepAs.id
    arguments := [.word, .bool]
  }
  let expectedEdges : List SourceSpecializationWorklist.CallEdge := [
    { caller := entryKey, occurrence := call.id, callee := wordKey },
    { caller := entryKey, occurrence := call.id, callee := boolKey }
  ]
  match ← runOrThrow "contextual local proof calls" program
      [monomorphicRequest localProof] 3 with
  | .complete plan =>
      let caller ← match plan.specializations.filter fun specialized =>
          decide (specialized.key = entryKey) with
        | [specialized] => pure specialized
        | specializations => throw (IO.userError
            s!"localProof retained {specializations.length} entry specializations")
      let callees := plan.specializations.filter fun specialized =>
        specialized.declaration == keepAs.id
      let solved ← match caller.function.solvedRequirements.filter fun solved =>
          solved.id == requirement with
        | [solved] => pure solved
        | solved => throw (IO.userError
            s!"localProof retained {solved.length} solutions for its Eq requirement")
      let implementationEvidence := match solved.evidence with
        | .implementation _ => true
        | .assumption _ => false
      assertTrue (decide (
          plan.seedKeys = [entryKey] ∧
          plan.specializations.map (·.key) = [entryKey, wordKey, boolKey] ∧
          plan.callEdges = expectedEdges ∧
          plan.callEdges.eraseDups.length = 2 ∧
          plan.referenceEdges = [] ∧
          callees.length = 2 ∧
          (callees.all fun callee => callee.assumptions = [predicate]) ∧
          solved.predicate = predicate) && implementationEvidence)
        "local proof calls lost their assumptions, evidence, keys, or edges"
      match SourceCoreDirectLinking.validatePlan program plan with
      | .ok () => pure ()
      | .error error => throw (IO.userError
          s!"contextual local proof plan failed replay validation: {reprStr error}")
  | outcome => throw (IO.userError
      s!"contextual local proof calls expected complete, found {reprStr outcome}")

private def testQualifiedLocalSchemeCalls
    (program : CheckedProgram) : IO Unit := do
  let keep ← signatureNamed program "keep"
  let qualifiedLocal ← signatureNamed program "qualifiedLocal"
  let function ← functionFor program qualifiedLocal
  let binder ← match function.typedBody.nodes.findSome? fun
      | .statement { form := .letDecl binder (some _), .. } =>
          if binder.name == "f" then some binder else none
      | _ => none with
    | some binder => pure binder
    | none => throw (IO.userError "qualifiedLocal lost its f binder")
  let template ← match binder.schemeRequirements with
    | [requirement] => pure requirement
    | requirements => throw (IO.userError
        s!"qualifiedLocal retained {requirements.length} scheme requirements")
  let (call, instantiation) ← match
      function.typedBody.nodes.findSome? fun
        | .expression node@{
            form := .call _ _ (.declaration instantiation), .. } =>
            if instantiation.declaration == keep.id then
              some (node, instantiation)
            else
              none
        | _ => none with
    | some selected => pure selected
    | none => throw (IO.userError "qualifiedLocal lost its keep call")
  assertTrue (decide (instantiation.predicates = [template.predicate] ∧
      call.requirements.contains template.templateRequirement))
    "qualifiedLocal detached its template predicate from the keep call"
  let entryKey : SourceSpecialization.SpecializationKey := {
    declaration := qualifiedLocal.id
    arguments := []
  }
  let wordKey : SourceSpecialization.SpecializationKey := {
    declaration := keep.id
    arguments := [.word]
  }
  let boolKey : SourceSpecialization.SpecializationKey := {
    declaration := keep.id
    arguments := [.bool]
  }
  let expectedEdges : List SourceSpecializationWorklist.CallEdge := [
    { caller := entryKey, occurrence := call.id, callee := wordKey },
    { caller := entryKey, occurrence := call.id, callee := boolKey }
  ]
  match ← runOrThrow "qualified local scheme calls" program
      [monomorphicRequest qualifiedLocal] 3 with
  | .complete plan =>
      let caller ← match plan.specializations.filter fun specialized =>
          decide (specialized.key = entryKey) with
        | [specialized] => pure specialized
        | specialized => throw (IO.userError
            s!"qualifiedLocal retained {specialized.length} entry specializations")
      let templateSolved ← match caller.function.solvedRequirements.filter
          fun solved => solved.id == template.templateRequirement with
        | [solved] => pure solved
        | solved => throw (IO.userError
            s!"qualifiedLocal retained {solved.length} template solutions")
      let templateAssumption := match templateSolved.evidence with
        | .assumption predicate => predicate == template.predicate
        | .implementation _ => false
      assertTrue (decide (
          plan.seedKeys = [entryKey] ∧
          plan.specializations.map (·.key) = [entryKey, wordKey, boolKey] ∧
          plan.callEdges = expectedEdges ∧
          plan.referenceEdges = [] ∧
          templateSolved.predicate = template.predicate) && templateAssumption)
        "qualified local scheme calls lost template evidence, keys, or edges"
      match SourceCoreDirectLinking.validatePlan program plan with
      | .ok () => pure ()
      | .error error => throw (IO.userError
          s!"qualified local plan failed canonical replay: {reprStr error}")
  | outcome => throw (IO.userError
      s!"qualified local scheme calls expected complete, found {reprStr outcome}")

  let wrongPredicate := {
    template.predicate with arguments := [.word]
  }
  let malformedBinderFunction : CheckedFunction := {
    function with
    typedBody := {
      function.typedBody with
      nodes := setLocalBinderRequirements function.typedBody.nodes binder.id [{
        template with predicate := wrongPredicate
      }]
    }
  }
  match SourceSpecializationWorklist.run
      (replaceFunction program malformedBinderFunction)
      [monomorphicRequest qualifiedLocal] 3 with
  | .error (.specialization declaration
      (.localSchemeRequirementPredicateMismatch actualBinder actualRequirement
        _ _)) =>
      assertTrue (decide (declaration = qualifiedLocal.id ∧
          actualBinder = binder.id ∧
          actualRequirement = template.templateRequirement))
        "qualified binder predicate tamper lost its owner or template identity"
  | result => throw (IO.userError
      s!"tampered qualified binder predicate was accepted: {reprStr result}")

  let detachedCallFunction : CheckedFunction := {
    function with
    typedBody := {
      function.typedBody with
      nodes := setExpressionRequirements function.typedBody.nodes call.id []
    }
  }
  match SourceSpecializationWorklist.run
      (replaceFunction program detachedCallFunction)
      [monomorphicRequest qualifiedLocal] 3 with
  | .error (.localSchemeRequirementIdMultiplicity _ actualRequirement 0) =>
      assertTrue (actualRequirement == template.templateRequirement)
        "detached qualified requirement lost its template identity"
  | result => throw (IO.userError
      s!"detached qualified call requirement was accepted: {reprStr result}")

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
  testContextualLocalPolymorphicCalls program
  testDepthTwoContextualLocalPolymorphicCalls program
  testGroundInnerUnderPolymorphicOuter program
  testSiblingContextualLocalPolymorphicCalls program
  testDepthThreeContextualLocalPolymorphicCalls program
  testScopeAwareRecursiveContextualLocalPolymorphicCalls program
  testMixedScopeDepthThreeContextualLocalPolymorphicCalls program
  testReusedBinderMixedScopeContextualLocalPolymorphicCalls program
  testMonomorphicLambdaWrapperContextualLocal program
  testUnusedNestedContextualLocal program
  testDerivedCanonicalization program
  testTypedNodeOrder program
  testRecursiveKeys program
  testAssumptionPreservation program
  testContextualLocalProofCalls program
  testQualifiedLocalSchemeCalls program
  testFunctionValueReference program
  testIndirectCallBoundary program
  testIndirectArgumentCounts program
  testMalformedTypedMetadata program

end Tests.SourceSpecializationWorklist
