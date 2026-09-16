import Solcore.Frontend.SourceSpecialization
import Solcore.Frontend.SourceCoreElaboration
import Solcore.Core.Machine

/-! End-to-end and rejection regressions for closing checked generic source
functions at concrete declaration arguments. -/

set_option autoImplicit false

namespace Tests.SourceSpecialization

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
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
    "function phantom<T, U>(value: T) returns (T) { return value; }",
    "function apply<T>(f: function(T) returns (T), value: T) returns (T) { return f(value); }"
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
  assertTrue (decide (specialized.key.arguments = [.bool] ∧
      specialized.parameterSubstitution = [(parameter, .bool)]))
    "identity did not retain its Bool specialization key"
  let elaborated ← elaborateOrThrow "identity" specialized.function
  assertTrue (decide (Core.infer? elaborated.inputs.values elaborated.core =
      some .bool ∧ Core.runStateful 16
        (.initial elaborated.core [.bool true]) = .done (.bool true) []))
    "Bool identity did not typecheck and execute"

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
  testPhantomParameter program
  testIndirectMetadataSpecialization program
  testValidationErrors program

end Tests.SourceSpecialization
