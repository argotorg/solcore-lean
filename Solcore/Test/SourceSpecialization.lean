import Solcore.Frontend.SourceSpecialization
import Solcore.Frontend.SourceCoreElaboration
import Solcore.Core.Machine

/-! End-to-end and rejection regressions for closing checked generic source
functions at concrete declaration arguments. -/

set_option autoImplicit false

namespace Tests.SourceSpecialization

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.Frontend.SourceStageAnalysis
open Solcore.TypeSystem

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private def checkedProgram : IO CheckedProgram := do
  let content := String.intercalate "\n" [
    "function select<A, B>(left: A, right: B) returns (A) { return left; }",
    "function identity<T>(value: T) returns (T) { return value; }",
    "function stagedIdentity<T>(comptime value: T) returns (comptime<T>) { return value; }",
    "function phantom<T, U>(value: T) returns (T) { return value; }",
    "function apply<T>(f: function(T) returns (T), value: T) returns (T) { return f(value); }",
    "function localPoly(flag: Bool) returns (Word, Bool) {",
    "  let id = lam(value) { return value; };",
    "  return (id(1), id(flag));",
    "}"
  ]
  match checkProgram (workspace content) with
  | .ok checked => pure checked
  | .error errors => throw (IO.userError
      s!"specialization fixture failed checking: {reprStr errors}")

private def checkedNamed (program : CheckedProgram) (name : String) :
    IO (ProgramFunctionSignature × CheckedFunction) := do
  let signatures := program.signatures.functions.filter fun signature =>
    signature.name == name
  let signature ← match signatures with
    | [signature] => pure signature
    | _ => throw (IO.userError
        s!"expected one signature named `{name}`, found {signatures.length}")
  let functions := program.functions.filter fun function =>
    function.declaration == signature.id
  match functions with
  | [function] => pure (signature, function)
  | _ => throw (IO.userError
      s!"expected one checked body named `{name}`, found {functions.length}")

private def word (value : Nat) : Core.Word :=
  ⟨value % Core.wordModulus, Nat.mod_lt _ (by simp [Core.wordModulus])⟩

private def specializeOrThrow (label : String)
    (signature : ProgramFunctionSignature) (function : CheckedFunction)
    (supplied : ParameterSubstitution) :
    IO Solcore.Frontend.SourceSpecialization.SpecializedFunction := do
  match Solcore.Frontend.SourceSpecialization.specializeFunction
      signature function supplied with
  | .ok specialized => pure specialized
  | .error error => throw (IO.userError
      s!"{label}: specialization failed: {reprStr error}")

private def elaborateOrThrow (label : String) (function : CheckedFunction) :
    IO SourceCoreElaboration.ElaboratedFunction := do
  match SourceCoreElaboration.elaborateFunction function with
  | .ok elaborated => pure elaborated
  | .error error => throw (IO.userError
      s!"{label}: specialized body did not lower: {reprStr error}")

private def expectError (label : String)
    (actual : Except Solcore.Frontend.SourceSpecialization.Error
      Solcore.Frontend.SourceSpecialization.SpecializedFunction)
    (expected : Solcore.Frontend.SourceSpecialization.Error) : IO Unit := do
  match actual with
  | .ok _ => throw (IO.userError
      s!"{label}: invalid specialization was accepted")
  | .error error =>
      assertTrue (decide (error = expected))
        s!"{label}: expected {reprStr expected}, found {reprStr error}"

private def testSelect (program : CheckedProgram) : IO Unit := do
  let (signature, function) ← checkedNamed program "select"
  let (a, b) ← match signature.scheme.parameters with
    | [a, b] => pure (a, b)
    | parameters => throw (IO.userError
        s!"select lost its two parameters: {reprStr parameters}")
  let supplied : ParameterSubstitution := [(b, .bool), (a, .word)]
  let specialized ← specializeOrThrow "select" signature function supplied
  assertTrue (decide (
      specialized.key.declaration = signature.id ∧
      specialized.key.arguments = [.word, .bool] ∧
      specialized.declaration = function.declaration ∧
      specialized.parameterSubstitution = [(a, .word), (b, .bool)] ∧
      specialized.function.declaration = function.declaration ∧
      specialized.function.typedBody.owner = function.typedBody.owner ∧
      specialized.function.typedBody.roots = function.typedBody.roots ∧
      specialized.function.typedBody.nodes.map Node.id =
        function.typedBody.nodes.map Node.id))
    "select did not canonicalize arguments or preserve source identities"
  let elaborated ← elaborateOrThrow "select" specialized.function
  assertTrue (decide (elaborated.inputs.values = [.word, .bool] ∧
      elaborated.returnType = .word ∧
      Core.infer? elaborated.inputs.values elaborated.core = some .word))
    "select did not elaborate to its concrete Core signature"
  assertTrue (decide (Core.runStateful 32
      (.initial elaborated.core [.word (word 41), .bool true]) =
        .done (.word (word 41)) []))
    "specialized select did not return its Word input"

private def testIdentity (program : CheckedProgram) : IO Unit := do
  let (signature, function) ← checkedNamed program "identity"
  let parameter ← match signature.scheme.parameters with
    | [parameter] => pure parameter
    | parameters => throw (IO.userError
        s!"identity lost its parameter: {reprStr parameters}")
  let specialized ← specializeOrThrow "identity" signature function
    [(parameter, .bool)]
  let boolInput ← match specialized.function.typedBody.inputs with
    | [input] => pure input
    | inputs => throw (IO.userError
        s!"Bool identity retained {inputs.length} inputs")
  assertTrue (decide (specialized.key.arguments = [.bool] ∧
      specialized.parameterSubstitution = [(parameter, .bool)] ∧
      specialized.stageAnalysis.binderStage? boolInput.id = some .runtime))
    "identity did not retain its Bool specialization key"
  let elaborated ← elaborateOrThrow "identity" specialized.function
  assertTrue (decide (Core.infer? elaborated.inputs.values elaborated.core =
      some .bool ∧ Core.runStateful 16
        (.initial elaborated.core [.bool true]) = .done (.bool true) []))
    "Bool identity did not typecheck and execute"
  let integerSpecialized ← specializeOrThrow "integer identity" signature function
    [(parameter, .integer)]
  let integerInput ← match integerSpecialized.function.typedBody.inputs with
    | [input] => pure input
    | inputs => throw (IO.userError
        s!"integer identity retained {inputs.length} inputs")
  assertTrue (decide
      (integerSpecialized.stageAnalysis.binderStage? integerInput.id =
        some .comptime))
    "specialization did not recompute an integer input as comptime-only"

private def testStagedIdentityMarkers (program : CheckedProgram) : IO Unit := do
  let (signature, function) ← checkedNamed program "stagedIdentity"
  let parameter ← match signature.scheme.parameters with
    | [parameter] => pure parameter
    | parameters => throw (IO.userError
        s!"stagedIdentity lost its parameter: {reprStr parameters}")
  let input ← match function.typedBody.inputs with
    | [input] => pure input
    | inputs => throw (IO.userError
        s!"stagedIdentity retained {inputs.length} inputs")
  assertTrue (decide (signature.parameterComptime = [true] ∧
      signature.returnComptime ∧ input.comptime ∧
      function.returnComptime ∧
      signature.scheme.body = .function (.parameter parameter)
        (.parameter parameter)))
    "generic comptime contract did not reach the checked carrier"
  let specialized ← specializeOrThrow "stagedIdentity" signature function
    [(parameter, .word)]
  let specializedInput ← match specialized.function.typedBody.inputs with
    | [input] => pure input
    | inputs => throw (IO.userError
        s!"specialized stagedIdentity retained {inputs.length} inputs")
  assertTrue (decide (specialized.function.type = .function .word .word ∧
      specializedInput.scheme = .mono .word ∧ specializedInput.comptime ∧
      specialized.function.returnComptime ∧
      specialized.stageAnalysis.binderStage? specializedInput.id =
        some .comptime))
    "specialization changed comptime flags or left them in semantic types"

private def testPhantomParameter (program : CheckedProgram) : IO Unit := do
  let (signature, function) ← checkedNamed program "phantom"
  let (t, unused) ← match signature.scheme.parameters with
    | [t, unused] => pure (t, unused)
    | parameters => throw (IO.userError
        s!"phantom lost its two parameters: {reprStr parameters}")
  let specialized ← specializeOrThrow "phantom" signature function
    [(unused, .word), (t, .bool)]
  assertTrue (decide (specialized.key.arguments = [.bool, .word] ∧
      specialized.parameterSubstitution = [(t, .bool), (unused, .word)]))
    "the unused declaration parameter disappeared from the canonical key"
  let elaborated ← elaborateOrThrow "phantom" specialized.function
  assertTrue (decide (Core.runStateful 16
      (.initial elaborated.core [.bool false]) = .done (.bool false) []))
    "phantom specialization did not execute at its used Bool parameter"

private def testIndirectMetadataSpecialization
    (program : CheckedProgram) : IO Unit := do
  let (signature, function) ← checkedNamed program "apply"
  let parameter ← match signature.scheme.parameters with
    | [parameter] => pure parameter
    | parameters => throw (IO.userError
        s!"apply lost its generic parameter: {reprStr parameters}")
  let specialized ← specializeOrThrow "apply" signature function
    [(parameter, .word)]
  let calls := specialized.function.typedBody.nodes.filterMap fun
    | .expression node =>
        match node.form with
        | .call _ _ (.indirect metadata) => some (node, metadata)
        | _ => none
    | .statement _ => none
  match calls with
  | [(node, metadata)] =>
      assertTrue (decide (node.type = .word ∧ node.coercions = [] ∧
          metadata.argumentTypeBeforeCoercion = .word ∧
          metadata.argumentTypeAfterCoercion = .word ∧
          metadata.argumentCoercions = [] ∧
          metadata.hasValidArgumentCoercionPath))
        "specialization did not close indirect call metadata at Word"
  | _ => throw (IO.userError
      s!"expected one specialized indirect call, found {calls.length}")

private def replaceExpression (function : CheckedFunction)
    (id : ExpressionId) (change : ExpressionNode → ExpressionNode) :
    CheckedFunction := {
  function with typedBody := {
    function.typedBody with
    nodes := function.typedBody.nodes.map fun
      | .expression node =>
          if node.id = id then .expression { change node with id }
          else .expression node
      | .statement node => .statement node
  }
}

private def replaceStatement (function : CheckedFunction)
    (id : StatementId) (change : StatementNode → StatementNode) :
    CheckedFunction := {
  function with typedBody := {
    function.typedBody with
    nodes := function.typedBody.nodes.map fun
      | .expression node => .expression node
      | .statement node =>
          if node.id = id then .statement { change node with id }
          else .statement node
  }
}

private def testLocalPolymorphicLambda
    (program : CheckedProgram) : IO Unit := do
  let (signature, function) ← checkedNamed program "localPoly"
  let bindings := function.typedBody.nodes.filterMap fun
    | .statement node@{ form := .letDecl binder (some initializer), .. } =>
        if binder.name == "id" then some (node, binder, initializer) else none
    | _ => none
  let (statement, binder, initializer) ← match bindings with
    | [binding] => pure binding
    | _ => throw (IO.userError
        "localPoly lost its unique initialized id binder")
  let quantified ← match binder.scheme.quantified with
    | [quantified] => pure quantified
    | variables => throw (IO.userError
        s!"localPoly id has the wrong quantified variables: {reprStr variables}")
  let lambdaNode ← match function.typedBody.lookupExpression? initializer with
    | some node@{ form := .lambda [_] _ _, .. } => pure node
    | _ => throw (IO.userError
        "localPoly id initializer is not a direct unary lambda")
  let specialized ← specializeOrThrow "local polymorphic lambda"
    signature function []
  let specializedBinder ← match specialized.function.typedBody.lookupStatement?
      statement.id with
    | some { form := .letDecl selected (some selectedInitializer), .. } =>
        if selectedInitializer = initializer then pure selected
        else throw (IO.userError
          "specialization changed the polymorphic initializer identity")
    | _ => throw (IO.userError
        "specialization changed the polymorphic let shape")
  let (specializedLambda, specializedParameter, specializedReturnType) ← match
      specialized.function.typedBody.lookupExpression? initializer with
    | some node@{ form := .lambda [parameter] returnType _, .. } =>
        pure (node, parameter, returnType)
    | _ => throw (IO.userError
        "specialization changed the direct lambda initializer")
  assertTrue (Solcore.Frontend.SourceSpecialization.isDirectLambdaInitializer
      specialized.function.typedBody initializer)
    "specialization no longer recognizes the direct lambda initializer"
  assertTrue (decide (specializedBinder.scheme = binder.scheme ∧
      specializedLambda.type = lambdaNode.type ∧
      specializedParameter.scheme.quantified = [] ∧
      specializedParameter.scheme.body = Ty.variable quantified ∧
      specializedReturnType = Ty.variable quantified ∧
      specialized.function.substitution.any fun entry =>
        entry.2 = .variable quantified))
    "specialization did not retain the principal lambda scheme and lexical residual"
  let instantiatedReferenceTypes := specialized.function.typedBody.nodes.filterMap fun
    | .expression node =>
        match node.form with
        | .reference _ (.local selected) =>
            if selected = binder.id then some node.type else none
        | _ => none
    | .statement _ => none
  assertTrue (instantiatedReferenceTypes.length == 2 &&
      instantiatedReferenceTypes.any (· == .function .word .word) &&
      instantiatedReferenceTypes.any (· == .function .bool .bool))
    "polymorphic references outside the initializer did not remain ground"

  let fresh : TypeVarId := ⟨991⟩
  let quantifiedParameter : TypedBinder := {
    specializedParameter with
    scheme := {
      quantified := [fresh]
      body := specializedParameter.scheme.body
    }
  }
  let badLambdaParameter := replaceExpression function initializer fun node =>
    match node.form with
    | .lambda _ returnType body => {
        node with form := .lambda [quantifiedParameter] returnType body
      }
    | _ => node
  expectError "quantified lambda parameter"
    (Solcore.Frontend.SourceSpecialization.specializeFunction signature
      badLambdaParameter [])
    (.polymorphicBinder quantifiedParameter.id [fresh])

  let uninitialized := replaceStatement function statement.id fun node => {
    node with form := .letDecl binder none
  }
  expectError "uninitialized polymorphic let"
    (Solcore.Frontend.SourceSpecialization.specializeFunction signature
      uninitialized [])
    (.polymorphicBinder binder.id [quantified])

  let indirectInitializer := replaceExpression function initializer fun node => {
    node with form := .proxy node.type
  }
  expectError "non-lambda polymorphic initializer"
    (Solcore.Frontend.SourceSpecialization.specializeFunction signature
      indirectInitializer [])
    (.polymorphicBinder binder.id [quantified])

  let forItem : ForItemForm := .letDecl binder (some initializer)
  let forBinder := replaceStatement function statement.id fun node => {
    node with form := .forLoop [forItem] initializer [] []
  }
  expectError "polymorphic for binder"
    (Solcore.Frontend.SourceSpecialization.specializeFunction signature
      forBinder [])
    (.polymorphicBinder binder.id [quantified])

  let pattern : TypedMatchPattern := {
    source := .binder statement.span binder.name
    type := binder.scheme.body
    resolution := .binder binder
  }
  let patternBinder := replaceStatement function statement.id fun node => {
    node with form := .matchWith {
      scrutinee := initializer
      hiddenScrutinee := binder.id
      cases := [{ span := statement.span, pattern, body := [] }]
      defaultBody := none
    }
  }
  expectError "polymorphic pattern binder"
    (Solcore.Frontend.SourceSpecialization.specializeFunction signature
      patternBinder [])
    (.polymorphicBinder binder.id [quantified])

  let leakedInput ← match function.typedBody.inputs with
    | [input] => pure { input with scheme := .mono (Ty.variable quantified) }
    | inputs => throw (IO.userError
        s!"localPoly retained {inputs.length} inputs")
  let leaked : CheckedFunction := {
    function with typedBody := {
      function.typedBody with inputs := [leakedInput]
    }
  }
  expectError "lexically escaped quantified variable"
    (Solcore.Frontend.SourceSpecialization.specializeFunction signature leaked [])
    (.residualType (.flexible quantified))

  let unboundVariable : TypeVarId := ⟨992⟩
  let unbound : CheckedFunction := {
    function with substitution :=
      function.substitution ++
        [(unboundVariable, Ty.variable unboundVariable)]
  }
  expectError "unbound substitution residual"
    (Solcore.Frontend.SourceSpecialization.specializeFunction signature unbound [])
    (.residualType (.flexible unboundVariable))

private def returnedExpression (function : CheckedFunction) : IO ExpressionId :=
  match function.typedBody.roots with
  | [.statement statement] =>
      match function.typedBody.lookupStatement? statement with
      | some { form := .returnStmt (some expression), .. } => pure expression
      | _ => throw (IO.userError
          "integer-specialization fixture root is not a valued return")
  | _ => throw (IO.userError
      "integer-specialization fixture does not have one statement root")

private def testIntegerLiteralMetadataSpecialization
    (program : CheckedProgram) : IO Unit := do
  let (signature, function) ← checkedNamed program "identity"
  let parameter ← match signature.scheme.parameters with
    | [parameter] => pure parameter
    | parameters => throw (IO.userError
        s!"identity lost its integer-metadata parameter: {reprStr parameters}")
  let expression ← returnedExpression function
  let requirement : RequirementId := ⟨211⟩
  let resolution : IntegerLiteralResolution := {
    rawValue := 9
    targetType := .parameter parameter
    requirement
  }
  let predicate := resolution.predicate
  let carrier := replaceExpression function expression fun node => {
    node with
    form := .integerLiteral (.decimal "9") resolution
    requirements := [requirement]
  }
  let carrier : CheckedFunction := {
    carrier with solvedRequirements := [{
      id := requirement
      predicate
      evidence := .implementation
        (.byImpl predicate (.builtin .intWord) [])
    }]
  }
  let specialized ← specializeOrThrow "integer metadata" signature carrier
    [(parameter, .word)]
  let closedNode ← match specialized.function.typedBody.lookupExpression?
      expression with
    | some node => pure node
    | none => throw (IO.userError
        "specialization lost the integer-literal expression")
  match closedNode.form with
  | .integerLiteral source closed =>
      assertTrue (decide (source = .decimal "9" ∧
          closed.rawValue = 9 ∧ closed.targetType = .word ∧
          closed.requirement = requirement ∧
          closed.predicate = ProgramSignatures.builtinIntPredicate .word ∧
          specialized.function.solvedRequirements.map (·.predicate) =
            [ProgramSignatures.builtinIntPredicate .word] ∧
          specialized.function.solvedRequirements.map (·.evidence.goal) =
            [ProgramSignatures.builtinIntPredicate .word]))
        "rigid specialization did not close integer metadata and evidence together"
  | _ => throw (IO.userError
      "rigid specialization changed the integer-literal expression form")
  let elaborated ← elaborateOrThrow "integer metadata" specialized.function
  assertTrue (decide (Core.runStateful 16
      (.initial elaborated.core [.word (word 99)]) =
        .done (.word (word 9)) []))
    "specialized integer literal did not execute through builtin Int<Word>"
  let unknown : TypeParameterId := ⟨signature.id, 99⟩
  let hidden := replaceExpression function expression fun node => {
    node with form := .integerLiteral (.decimal "9") {
      resolution with targetType := .parameter unknown
    }
  }
  expectError "hidden integer target"
    (Solcore.Frontend.SourceSpecialization.specializeFunction signature hidden
      [(parameter, .word)])
    (.undeclaredObservedParameter unknown)

private def testValidationErrors (program : CheckedProgram) : IO Unit := do
  let (signature, function) ← checkedNamed program "select"
  let (identitySignature, identityFunction) ← checkedNamed program "identity"
  let (a, b) ← match signature.scheme.parameters with
    | [a, b] => pure (a, b)
    | parameters => throw (IO.userError
        s!"select lost its validation parameters: {reprStr parameters}")
  let foreign ← match identitySignature.scheme.parameters with
    | [parameter] => pure parameter
    | parameters => throw (IO.userError
        s!"identity lost its validation parameter: {reprStr parameters}")
  let specialize := Solcore.Frontend.SourceSpecialization.specializeFunction
    signature function
  expectError "missing parameter" (specialize [(a, .word)])
    (.missingSuppliedParameter b)
  expectError "duplicate parameter"
    (specialize [(a, .word), (a, .word), (b, .bool)])
    (.duplicateSuppliedParameter a)
  let unknown : TypeParameterId := ⟨signature.id, 100⟩
  expectError "unknown parameter"
    (specialize [(a, .word), (b, .bool), (unknown, .word)])
    (.unknownSuppliedParameter unknown)
  expectError "foreign parameter"
    (specialize [(a, .word), (b, .bool), (foreign, .word)])
    (.suppliedParameterOwnerMismatch signature.id foreign)
  let metavariable : TypeVarId := ⟨77⟩
  expectError "non-ground argument"
    (specialize [(a, .variable metavariable), (b, .bool)])
    (.nonConcreteArgument a (.flexible metavariable))
  expectError "declaration mismatch"
    (Solcore.Frontend.SourceSpecialization.specializeFunction
      signature identityFunction [(a, .word), (b, .bool)])
    (.declarationMismatch signature.id identityFunction.declaration)
  let (firstInput, secondInput) ← match function.typedBody.inputs with
    | [first, second] => pure (first, second)
    | inputs => throw (IO.userError
        s!"select lost its two input binders: {inputs.length}")
  let markedInput : TypedBinder := { firstInput with comptime := true }
  let wrongParameterComptime : CheckedFunction := {
    function with typedBody := {
      function.typedBody with inputs := [markedInput, secondInput]
    }
  }
  expectError "parameter comptime mismatch"
    (Solcore.Frontend.SourceSpecialization.specializeFunction
      signature wrongParameterComptime [(a, .word), (b, .bool)])
    (.parameterComptimeMismatch [false, false] [true, false])
  let wrongReturnComptime : CheckedFunction := {
    function with returnComptime := true
  }
  expectError "return comptime mismatch"
    (Solcore.Frontend.SourceSpecialization.specializeFunction
      signature wrongReturnComptime [(a, .word), (b, .bool)])
    (.returnComptimeMismatch false true)
  let openVariable : TypeVarId := ⟨78⟩
  let bound : TypeVarId := ⟨79⟩
  let openInput : TypedBinder := {
    firstInput with scheme := .mono (.variable openVariable)
  }
  let polymorphicInput : TypedBinder := {
    secondInput with scheme := { quantified := [bound], body := .variable bound }
  }
  let polymorphic : CheckedFunction := {
    function with typedBody := {
      function.typedBody with inputs := [openInput, polymorphicInput]
    }
  }
  expectError "polymorphic local boundary"
    (Solcore.Frontend.SourceSpecialization.specializeFunction signature
      polymorphic [(b, .bool), (a, .word)])
    (.polymorphicBinder secondInput.id [bound])
  let predicate : ProgramPredicate := {
    trait := signature.id
    subject := .word
    arguments := []
  }
  let goal : ProgramPredicate := { predicate with subject := .bool }
  let requirement : SolvedRequirement := {
    id := ⟨19⟩
    predicate
    evidence := .assumption goal
  }
  let malformed : CheckedFunction := {
    function with solvedRequirements := [requirement]
  }
  expectError "evidence goal mismatch"
    (Solcore.Frontend.SourceSpecialization.specializeFunction signature malformed
      [(b, .bool), (a, .word)])
    (.evidenceGoalMismatch requirement.id predicate goal)

/-- Exercise canonical specialization, Core execution, phantom declaration
parameters, and exact boundary errors from a checked raw workspace. -/
def testSourceSpecialization : IO Unit := do
  let program ← checkedProgram
  testSelect program
  testIdentity program
  testStagedIdentityMarkers program
  testPhantomParameter program
  testIndirectMetadataSpecialization program
  testLocalPolymorphicLambda program
  testIntegerLiteralMetadataSpecialization program
  testValidationErrors program

end Tests.SourceSpecialization
