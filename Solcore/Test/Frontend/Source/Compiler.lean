import Solcore.Test.Frontend.Source.CompilerFeatureSupport
import Solcore.Test.SourceSemantics.CoreLowering.Foundations.EntryPoints
import Solcore.Frontend.SourceCoreCompiler
import Solcore.Frontend.SourceCoreIndexedSession
import Solcore.Frontend.Internal.RuntimeValidation
import Solcore.Frontend.SourceCoreExecution
import Solcore.Frontend.SourceCore.RawMetadata
import Solcore.Frontend.SourceCore.Compatible
import Solcore.Frontend.SourceCoreUnified
import Solcore.Frontend.SourceInference
import Solcore.Frontend.SourceCore.Internal.DirectLinking
import Solcore.Frontend.Internal.RuntimeValues

/-!
# Source compiler tests

The public source compiler: its single Core, value and session boundary, routing, retained boundaries,
constructor visibility and program execution.
-/

section
-- leanmerge: from Solcore.Test.SourceCompilerAssignments
/-! Assignment regressions use public values and opaque checkpoints; the same
cached artifact supplies source-cell and complete-native-store effect audits. -/
set_option autoImplicit false
namespace Tests.SourceCompilerAssignments
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Tests.SourceCompilerFeatureSupport

private def success (entry : Entry) (arguments : List Value)
    (expected : Value) : IO (List SourceTypedRuntime.Cell) := do
  require ((← entry.run arguments) == expected) "public assignment changed its result"
  entry.checkResume arguments expected
  let complete ← entry.audit arguments
  let pending ← entry.audit arguments 10
  match ← nativeObservation pending with
  | .outOfFuel _ => pure ()
  | _ => throw (IO.userError "native assignment did not suspend")
  let resumed ← get "native assignment resume" (pending.resume 300000)
  require ((← nativeObservation resumed) == (← nativeObservation complete))
    "assignment resume changed its snapshot or complete shared native store"
  pure (sourceState complete).heap

private def expectedDiagnostic (program : CheckedProgram) (name : String)
    (error : SourceTypedRuntime.RuntimeError) : IO SourceCoreFaultSites.Diagnostic := do
  let declaration ← match program.signatures.functions.find? (·.name == name) with
    | some signature => pure signature.id
    | none => throw (IO.userError "public assignment diagnostic owner missing")
  let function ← match program.functions.find? (·.declaration == declaration) with
    | some function => pure function
    | none => throw (IO.userError "public assignment source missing")
  match function.typedBody.nodes.find? (fun
      | .statement node => match node.form with
        | .assignValue _ operator _ => operator != .equal
        | .assignBitNot _ | .forLoop .. => true
        | _ => false
      | _ => false) with
  | some (.statement node) => pure { error, site := .occurrence node.id.occurrence, span := some node.span }
  | _ => throw (IO.userError "public assignment diagnostic occurrence missing")

private def failure (entry : Entry) (arguments : List Value)
    (diagnostic : SourceCoreFaultSites.Diagnostic) : IO (Core.Word × List SourceTypedRuntime.Cell) := do
  let invocation ← entry.invoke arguments
  match invocation.outcome with
  | .failed reason _ =>
      require (reason != Core.Word.zero && decide ((← invocation.diagnostic reason) = some diagnostic))
        "assignment failure lost its exact source error, occurrence or span"
      let audit ← entry.audit arguments
      match audit.observation with
      | .fault error state =>
          require (decide (error = diagnostic.error)) "source observation changed failure priority"
          pure (reason, state.heap)
      | _ => throw (IO.userError "source observation lost the assignment failure")
  | _ => throw (IO.userError "public assignment did not fail")

private def hasWordCell (heap : List SourceTypedRuntime.Cell) (index : Nat) (expected : Core.Word) : Bool :=
  match heap[index]? with
  | some ⟨.word, some (.word actual)⟩ => actual == expected
  | _ => false

private def isAbsentWordCell (heap : List SourceTypedRuntime.Cell) (index : Nat) : Bool :=
  match heap[index]? with
  | some ⟨.word, none⟩ => true
  | _ => false

private def testProfile (program : CheckedProgram) : IO Unit := do
  let operators ← compileNamed program "operators"
  discard <| success operators [scalar 2] (.word (word 8).bitNot)
  discard <| success operators [scalar 5] (.word (word 14).bitNot)
  discard <| success (← compileNamed program "forOrder") [scalar 3] (.product (scalar 23) (scalar 3))
  for (name, error) in ([
      ("absent", .invalidAssignmentOperands .add none (some .word)),
      ("unaryAbsent", .invalidUnaryOperand .bitNot none),
      ("headerAbsent", .invalidAssignmentOperands .add none (some .word)),
      ("postAbsent", .invalidAssignmentOperands .add none (some .word)),
      ("unaryPostAbsent", .invalidUnaryOperand .bitNot none)] :
      List (String × SourceTypedRuntime.RuntimeError)) do
    let compiled ← compileNamed program name
    discard <| failure compiled [] (← expectedDiagnostic program name error)
  let choose ← compileNamed program "choose"
  let mut tokens : List Core.Word := []
  for (flag, name, operator) in [(true, "failLeft", Syntax.ValueAssignOp.add), (false, "failRight", .subtract)] do
    let (reason, _) ← failure choose [.bool flag] (← expectedDiagnostic program name
      (.invalidAssignmentOperands operator none (some .word)))
    tokens := reason :: tokens
  require (tokens[0]? != tokens[1]?) "public callee assignment failures reused a token"
  /- Closures capture by value: an RHS closure call writes only its own copy
  of the target. The copies follow the target in the source heap: the
  closure's snapshot copies, the closure, then the call's copies. -/
  let snapshot ← compileNamed program "snapshot"
  let store ← success snapshot [scalar 2] (scalar 5)
  /- `rhs` cannot change `value`, so this cell no longer shows whether the
  target was read before the RHS. -/
  require (hasWordCell store 0 (word 5))
    "public compound assignment changed its result or an RHS closure call reached its target"
  let absent ← compileNamed program "snapshotAbsent"
  let (_, store) ← failure absent [] (← expectedDiagnostic program "snapshotAbsent"
    (.invalidAssignmentOperands .add none (some .word)))
  require (isAbsentWordCell store 0 && hasWordCell store 3 (word 100))
    "public absent-operand failure discarded the RHS call's write to its copy, or the write reached the target"
  let priority ← compileNamed program "failurePriority"
  let function ← match program.functions.find? (·.declaration == priority.key.declaration) with
    | some function => pure function
    | none => throw (IO.userError "public RHS failure owner missing")
  let (node, binder) ← match function.typedBody.nodes.filterMap (fun
      | .expression node => match node.form with
        | .reference "absent" (.local binder) => some (node, binder)
        | _ => none
      | _ => none) with
    | [site] => pure site
    | _ => throw (IO.userError "public RHS failure occurrence missing")
  let (_, store) ← failure priority [] {
    error := .uninitializedLocal binder, site := .occurrence node.id.occurrence, span := some node.span }
  require (isAbsentWordCell store 0 && hasWordCell store 6 (word 100))
    "public RHS failure lost the call's preceding write to its copy, or the write reached the target"
  discard <| success (← compileNamed program "captured") [scalar 4] (.product (scalar 6) (scalar 7))
  discard <| success (← compileNamed program "functionEqual") [] (scalar 2)

def run : IO Unit := do
  let program ← get "assignment fixtures" (checkProgram Tests.SourceCoreAssignmentEntries.fixtures)
  testProfile program
end Tests.SourceCompilerAssignments
end

section
-- leanmerge: from Solcore.Test.SourceCompilerCoreCells
/-! One public compiler executes mutable locals. Allocation and failure effects
are also audited through the same cached Core artifact's source observer. -/
set_option autoImplicit false
namespace Tests.SourceCompilerCoreCells
open Solcore Solcore.Frontend Tests.SourceCompilerFeatureSupport

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "function mutate(flag: Bool, first: Word, second: Word) returns (Word, Bool) {",
    "  let value: Word; value = first; value = second; return (value, flag);",
    "}",
    "function replace<T>(first: T, second: T) returns (T) {",
    "  let value: T = first; value = second; return value;",
    "}",
    "function absent(input: Word) returns (Word) { let value: Word; return value; }",
    "function early(flag: Bool, initial: Word, replacement: Word) returns (Word) {",
    "  let value: Word = initial;",
    "  { let inner: Word = replacement; if (flag) { return value; } value = inner; }",
    "  value = replacement; return value;",
    "}",
    "function branchFailure(flag: Bool) returns (Word) {",
    "  let absent: Word; return flag ? absent : absent;",
    "}",
    "function chooseFailure(flag: Bool, value: Word) returns (Word) {",
    "  let absent: Word; return flag ? value : absent;",
    "}",
    "function arithmetic(initial: Word) returns (Word) {",
    "  let value: Word = initial + 2; value = value * 3; return value - 1;",
    "}",
    "function andFailure(flag: Bool) returns (Bool) {",
    "  let absent: Bool; return flag && absent;",
    "}",
    "function orFailure(flag: Bool) returns (Bool) {",
    "  let absent: Bool; return flag || absent;",
    "}",
    "function direct(input: Word) returns (Word) { return input; }",
    "function recurse(value: Word) returns (Word) {",
    "  return value == 0 ? 5 : recurse(value - 1);",
    "}"
  ] }]
  externalLibraries := []
}


private def localReads (program : CheckedProgram) (compiled : Entry) (name : String) :
    IO (List (SourceInference.ExpressionNode × Resolved.LocalId)) := do
  let function ← match program.functions.find? (·.declaration == compiled.key.declaration) with
    | some function => pure function | none => throw (IO.userError "diagnostic owner missing")
  pure (function.typedBody.nodes.filterMap fun
    | .expression node => match node.form with
      | .reference actual (.local binder) => if actual == name then some (node, binder) else none
      | _ => none
    | _ => none)

private def failAt (entry : Entry) (arguments : List Value) (node : SourceInference.ExpressionNode)
    (binder : Resolved.LocalId) : IO Core.Word := do
  let invocation ← entry.invoke arguments
  match invocation.outcome with
  | .failed token _ =>
      require (token != Core.Word.zero && decide ((← invocation.diagnostic token) = some {
        error := .uninitializedLocal binder, site := .occurrence node.id.occurrence, span := some node.span }))
        "public failure lost its exact source error, occurrence or span"
      pure token
  | _ => throw (IO.userError "uninitialized read did not fail")

private def testMutableReuse (program : CheckedProgram) : IO Unit := do
  let compiled ← compileNamed program "mutate"
  require (compiled.inputTypes == [.bool, .word, .word] && compiled.resultType == .product .word .bool)
    "public source signature metadata changed"
  for (flag, first, second) in [(true, 11, 29), (false, 2, 7)] do
    let arguments : List Value := [.bool flag, scalar first, scalar second]
    let expected : Value := .product (scalar second) (.bool flag)
    require ((← compiled.run arguments) == expected) "cached mutation reused a previous input frame"
    compiled.checkCells arguments [(.bool, some (.bool flag)), (.word, some (scalar first)),
      (.word, some (scalar second)), (.word, some (scalar second))]
    compiled.checkResume arguments expected

private def testSpecializationAndFailure (program : CheckedProgram) : IO Unit := do
  let pairType := TypeSystem.Ty.product .word (.product .bool .word)
  let compiled ← compileNamed program "replace" [pairType]
  let first : Value := .product (scalar 1) (.product (.bool false) (scalar 2))
  let second : Value := .product (scalar 8) (.product (.bool true) (scalar 9))
  require ((← compiled.run [first, second]) == second) "generic product assignment changed"
  compiled.checkCells [first, second] [(pairType, some first), (pairType, some second), (pairType, some second)]
  let artifact ← compiled.execution.open
  let session ← boot artifact
  match session.start compiled.key [first, .product (scalar 8) (.product (.bool true) (.bool false))] with
  | .error {code := .compatible {code := .sourceTypeMismatch .word .bool, ..}, path, ..} =>
      require (!path.isEmpty) "deep public rejection lost its argument path"
  | _ => throw (IO.userError "nested public shape mismatch was accepted")
  match session.start compiled.key [first] with
  | .error {code := .argumentCountMismatch 2 1, ..} => pure ()
  | .error error => throw (IO.userError s!"public arity diagnostic changed: {reprStr error}")
  | .ok _ => throw (IO.userError "public arity mismatch was accepted")
  -- Raw capability rejection is checked on the actual cached native entry.
  let native ← compiled.native
  let rawFirst : Core.Value := .pair (.word (word 1)) (.pair (.bool false) (.word (word 2)))
  match native.start [rawFirst, .pair (.word (word 8)) (.pair (.bool true) (.cellRef .word 0))] with
  | .error (.input 1 _) => pure ()
  | _ => throw (IO.userError "cached native entry accepted a nested external reference")
  match native.start [] [.word (word 3)] with
  | .error (.initialStoreUnsupported 1) => pure ()
  | _ => throw (IO.userError "cached native entry silently dropped an initial store")
  let absent ← compileNamed program "absent"
  let (node, binder) ← match ← localReads program absent "value" with
    | [site] => pure site | _ => throw (IO.userError "absent read site missing")
  discard <| failAt absent [scalar 4] node binder
  absent.checkCells [scalar 4] [(.word, some (scalar 4)), (.word, none)]

private def testControlAndDiagnostics (program : CheckedProgram) : IO Unit := do
  let early ← compileNamed program "early"
  for flag in [true, false] do
    let expected := if flag then scalar 11 else scalar 29
    let arguments : List Value := [.bool flag, scalar 11, scalar 29]
    require ((← early.run arguments) == expected) "early return or conditional fallthrough changed"
    early.checkCells arguments [(.bool, some (.bool flag)), (.word, some (scalar 11)),
      (.word, some (scalar 29)), (.word, some expected), (.word, some (scalar 29))]
  let branch ← compileNamed program "branchFailure"
  let (left, right) ← match ← localReads program branch "absent" with
    | [left, right] => pure (left, right) | _ => throw (IO.userError "two branch reads missing")
  require (decide (left.2 = right.2 ∧ left.1.id ≠ right.1.id ∧ left.1.span ≠ right.1.span))
    "branch fixture lost distinct read occurrences"
  let tokens ← [true, false].mapM fun flag => do
    let (node, binder) := if flag then left else right
    let token ← failAt branch [.bool flag] node binder
    branch.checkCells [.bool flag] [(.bool, some (.bool flag)), (.word, none)]
    pure token
  require (tokens[0]? != tokens[1]?) "different source reads shared a failure token"
  let invocation ← branch.invoke [.bool true]
  require (decide ((← invocation.diagnostic Core.Word.zero) = some {
    error := .functionFellThrough .word, site := .declaration branch.key.declaration, span := none }))
    "reserved fallthrough diagnostic changed"
  require ((← invocation.diagnostic (word 999)).isNone) "unknown reason resolved to a source diagnostic"
  let choose ← compileNamed program "chooseFailure"
  require ((← choose.run [.bool true, scalar 6]) == scalar 6) "conditional evaluated its untaken branch"
  choose.checkCells [.bool true, scalar 6] [(.bool, some (.bool true)), (.word, some (scalar 6)), (.word, none)]

private def testPrimitivesAndCalls (program : CheckedProgram) : IO Unit := do
  require ((← (← compileNamed program "direct").run [scalar 17]) == scalar 17) "direct result changed"
  require ((← (← compileNamed program "recurse").run [scalar 3]) == scalar 5) "recursive result changed"
  let arithmetic ← compileNamed program "arithmetic"
  for (initial, stored, expected) in ([(4, 18, 17), (0, 6, 5)] : List (Nat × Nat × Nat)) do
    require ((← arithmetic.run [scalar initial]) == scalar expected) "mutable literal arithmetic changed"
    arithmetic.checkCells [scalar initial] [(.word, some (scalar initial)), (.word, some (scalar stored))]
  for (name, shortValue, evaluatingValue) in [("andFailure", false, true), ("orFailure", true, false)] do
    let compiled ← compileNamed program name
    require ((← compiled.run [.bool shortValue]) == .bool shortValue) "short circuit evaluated its right operand"
    compiled.checkCells [.bool shortValue] [(.bool, some (.bool shortValue)), (.bool, none)]
    let (node, binder) ← match ← localReads program compiled "absent" with
      | [site] => pure site | _ => throw (IO.userError "right operand site missing")
    discard <| failAt compiled [.bool evaluatingValue] node binder
    compiled.checkCells [.bool evaluatingValue] [(.bool, some (.bool evaluatingValue)), (.bool, none)]

private def testFallthroughChecking : IO Unit := do
  let incomplete : Workspace.RawWorkspace := {
    entry := "main.solc", externalLibraries := []
    mainSources := [{ path := "main.solc", content :=
      "function incomplete(flag: Bool, input: Word) returns (Word) { if (flag) { return input; } }" }]
  }
  match checkProgram incomplete with
  | .error [.inference failure] =>
      match failure.error with
      | .unification (.mismatch actual expected) =>
          require (actual == .unit && expected == .word)
            "incomplete non-Unit function changed its checking rejection"
      | error => throw (IO.userError s!"incomplete function produced a different error: {reprStr error}")
  | .error errors => throw (IO.userError s!"incomplete function changed checking phase: {reprStr errors}")
  | .ok _ => throw (IO.userError "incomplete non-Unit function passed source checking")

example {definitions : Core.DataEnvironment} {type : Core.Ty}
    (result : SourceCoreGeneralEntry.Result definitions type) : result.observation.HasType type definitions := result.typed
example {artifact : SourceCoreExecution.Artifact} (done : SourceCoreExecution.Completion artifact) :
    done.session.Authenticates done.boundaryFuel done.sourceType done.value := done.typed

def run : IO Unit := do
  let program ← get "mutable locals checking" (checkProgram workspace)
  testMutableReuse program
  testSpecializationAndFailure program
  testControlAndDiagnostics program
  testPrimitivesAndCalls program
  testFallthroughChecking
end Tests.SourceCompilerCoreCells
end

section
-- leanmerge: from Solcore.Test.SourceCompilerCoreGeneral
/-! One cached compiler artifact supplies public data/function sessions and
internal native boundary checks. Metadata, ordered duplicates, captured values
and globals survive repeated invocation and checkpoint resumption; every call
of a closure starts again from the values it captured. -/
set_option autoImplicit false
namespace Tests.SourceCompilerCoreGeneral
open Solcore Solcore.Frontend Tests.SourceCompilerFeatureSupport

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "enum Tree { Leaf(Word), Pair(Tree, Tree) }",
    "enum Command { Create(Word), Invoke(function(Word) returns (Word), Word) }",
    "enum Reply { Made(function(Word) returns (Word)), Result(Word) }",
    "function inc(value: Word) returns (Word) { return value + 1; }",
    "function main(value: Word) returns (Tree) { return .Leaf(inc(value)); }",
    "function echo(value: Tree) returns (Tree) { return value; }",
    "function recurse(count: Word, value: Tree) returns (Tree) { return count == 0 ? value : recurse(count - 1, Tree.Pair(value, value)); }",
    "function mappingValue(table: mapping(Word => Word)) returns (mapping(Word => Word)) { table[7] += 3; return table; }",
    "function missing(table: mapping(Word => Tree), key: Word) returns (Tree) { return table[key]; }",
    "function absent() returns (Tree) { let value: Tree; return value; }",
    "function proxyValue() returns (@Tree) { return @Tree; }",
    "function makeAdder(value: Word) returns (function(Word) returns (Word)) { return lam(delta: Word) -> Word { value = value + delta; return inc(value); }; }",
    "function step(command: Command) returns (Reply) { match (command) {",
    " case .Create(value) { return .Made(lam(delta: Word) -> Word { value = value + delta; return inc(value); }); }",
    " case .Invoke(f, delta) { return .Result(f(delta)); } } }"
  ] }] }

private def metadata (program : CheckedProgram) (name : String) (index : Nat) : IO SourceInference.DataConstructorInstantiation := do
  let signature ← match program.signatures.dataTypes.filter (·.name == name) with
    | [signature] => pure signature
    | _ => throw (IO.userError s!"public general data signature missing: {name}")
  let constructor ← match signature.constructors[index]? with
    | some constructor => pure constructor
    | none => throw (IO.userError "public general constructor missing")
  pure ⟨constructor.id, [], constructor.payloadTypes, .nominal signature.id []⟩

private def ownedRun {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreExecution.Key)
    (argument : Value) : IO (SourceCoreExecution.Completion artifact) := do
  match ← get "owned invocation" (← session.run key [argument] executionOptions) with
  | .succeeded completion => pure completion
  | .exportError error _ => throw (IO.userError s!"owned result rejected: {reprStr error}")
  | _ => throw (IO.userError "owned invocation failed")

example (entry : Entry) : SourceCoreExecution.prepare entry.compiled = .ok entry.execution := entry.prepared
example {definitions : Core.DataEnvironment} {type : Core.Ty}
    (result : SourceCoreGeneralEntry.Result definitions type) :
    result.observation.HasType type definitions := result.typed

def run : IO Unit := do
  let program ← get "general source checking" (checkProgram workspace)
  let leafMetadata ← metadata program "Tree" 0
  let pairMetadata ← metadata program "Tree" 1
  let leaf := fun value => SourceCorePublicValues.Value.constructed leafMetadata [scalar value]
  let pair := fun left right => SourceCorePublicValues.Value.constructed pairMetadata [left, right]
  let main ← compileNamed program "main"
  require (main.cached.compatible.checked.catalog.definitions.length > 0)
    "nominal typing used an empty data environment"
  for _ in [0, 1] do
    require ((← main.run [scalar 8]) == leaf 9) "cached nominal run changed"
  let echo ← compileNamed program "echo"
  let tree := pair (leaf 3) (pair (leaf 4) (leaf 5))
  require ((← echo.run [tree]) == tree) "deep nominal public input/result changed"
  match (← echo.native).start [.constructed ⟨⟨999⟩, 0⟩ .unit] with
  | .error (.input 0 _) => pure ()
  | _ => throw (IO.userError "cached native entry accepted an unknown nominal identity")
  match (← main.native).start [.word (word 8)] [.unit] with
  | .error (.initialStoreUnsupported 1) => pure ()
  | _ => throw (IO.userError "fresh cached native entry accepted an unowned initial heap")
  let recursive ← compileNamed program "recurse"
  require ((← recursive.run [scalar 2, leaf 2]) ==
    pair (pair (leaf 2) (leaf 2)) (pair (leaf 2) (leaf 2))) "recursive execution changed"
  let mapping ← compileNamed program "mappingValue"
  let entries : List (Value × Value) := [(scalar 7, scalar 4), (scalar 7, scalar 99), (scalar 2, scalar 6)]
  require ((← mapping.run [.mapping .word .word entries]) == .mapping .word .word
    [(scalar 7, scalar 7), (scalar 7, scalar 99), (scalar 2, scalar 6)])
    "mapping duplicate order or latest write changed"
  let proxy ← compileNamed program "proxyValue"
  require ((← proxy.run []) == .proxy leafMetadata.resultType) "proxy lost raw inner identity"
  let function ← compileNamed program "makeAdder"
  match ← function.run [scalar 10] with
  | .function _ => pure ()
  | _ => throw (IO.userError "function return lost its owned handle")
  match ← nativeObservation (← function.audit [scalar 10]) with
  | .succeeded (.pair (.pair (.inLeft .word .unit) (.closure ..)) (.word contract)) _ =>
      require (contract != Core.Word.zero) "callable lost its authenticated contract descriptor"
  | _ => throw (IO.userError "cached function result changed native shape")
  for name in ["missing", "absent"] do
    let failed ← compileNamed program name
    let arguments : List Value := if name == "missing" then
      [.mapping .word leafMetadata.resultType [], scalar 7] else []
    let invocation ← failed.invoke arguments
    match invocation.outcome with
    | .failed reason _ =>
        match ← invocation.diagnostic reason with
        | some diagnostic =>
            require diagnostic.span.isSome "general failure lost occurrence span"
            if name == "missing" then
              require (decide (diagnostic.error = .typeMismatch leafMetadata.resultType none))
                "absent mapping default changed source error"
        | none => throw (IO.userError "general language failure lost its diagnostic")
    | _ => throw (IO.userError "general language failure changed")

  let conventional ← get "conventional general entry" (SourceCoreExecution.compileEntry workspace options)
  let conventionalRoot ← match conventional.root? 0 with
    | some root => pure root | none => throw (IO.userError "conventional root missing")
  let conventionalArtifact ← conventional.open
  let conventionalSession ← boot conventionalArtifact
  let conventionalResult ← ownedRun conventionalSession conventionalRoot.key (scalar 4)
  require (conventionalResult.value == leaf 5) "raw compileEntry changed conventional main"

  let step ← compileNamed program "step"
  let artifact ← step.execution.open
  require (step.execution.keys == [step.key]) "cached owned root key changed"
  let session ← boot artifact
  let createMetadata ← metadata program "Command" 0
  let invokeMetadata ← metadata program "Command" 1
  let madeMetadata ← metadata program "Reply" 0
  let resultMetadata ← metadata program "Reply" 1
  let made ← ownedRun session step.key (.constructed createMetadata [scalar 10])
  let handle ← match made.value with
    | .constructed actual [.function handle] =>
        require (decide (actual = madeMetadata)) "owned nominal result lost constructor metadata"
        pure handle
    | _ => throw (IO.userError "owned nominal function result changed shape")
  let invoked ← ownedRun made.session step.key (.constructed invokeMetadata [.function handle, scalar 2])
  require (invoked.value == .constructed resultMetadata [scalar 13])
    "cached artifact lost original global/capture references"
  let again ← ownedRun invoked.session step.key (.constructed invokeMetadata [.function handle, scalar 3])
  require (again.value == .constructed resultMetadata [scalar 14] && again.session.heapSize > invoked.session.heapSize)
    "owned session closure did not restart from its captured value across world extension"
  let checkpoint ← get "owned checkpoint" (again.session.start step.key
    [.constructed invokeMetadata [.function handle, scalar 1]])
  let next ← match ← checkpoint.resume 2 with
    | .outOfFuel next => pure next
    | _ => throw (IO.userError "owned checkpoint did not suspend")
  match ← next.resume 300000 with
  | .succeeded completion =>
      require (completion.value == .constructed resultMetadata [scalar 12]) "owned resume changed the captured value"
  | _ => throw (IO.userError "owned resume failed")
  let separate ← step.execution.open
  let other ← boot separate
  match other.authenticate 1024 invokeMetadata.resultType (.constructed invokeMetadata [.function handle, scalar 1]) with
  | .error {code := .foreignArtifact, ..} => pure ()
  | _ => throw (IO.userError "another cached artifact accepted the function capability")
  IO.println "public compiler data and owned sessions GREEN"
end Tests.SourceCompilerCoreGeneral
end

section
-- leanmerge: from Solcore.Test.SourceCompilerFunctions
set_option autoImplicit false
namespace Tests.SourceCompilerFunctions
open Solcore Solcore.Frontend Tests.SourceCompilerFeatureSupport

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "function inc(value: Word) returns (Word) { return value + 1; }",
    "function consume(f: function(Word) returns (Word), value: Word) returns (Word) { return f(value); }",
    "function named(value: Word) returns (Word) { return consume(inc, value); }",
    "function makeAdder(value: Word) returns (function(Word) returns (Word)) {",
    " return lam(delta: Word) -> Word { value = value + delta; return value; }; }",
    "function returned(value: Word) returns (Word, Word) {",
    " let f: function(Word) returns (Word) = makeAdder(value); return (f(2), f(3)); }",
    "function shared(value: Word) returns (Word, Word) {",
    " let f: function(Word) returns (Word) = lam(delta: Word) -> Word { value = value + delta; return value; };",
    " let g: function(Word) returns (Word) = lam(delta: Word) -> Word { value = value + delta; return value; }; return (f(2), g(3)); }",
    "function selfCell(value: Word) returns (Word) {",
    " let loop: function(Word) returns (Word);",
    " loop = lam(n: Word) -> Word { return n == 0 ? value : loop(n - 1); }; return loop(3); }",
    "function failure() returns (Word) { let f: function(Word) returns (Word); return f(0); }"
  ] }]
}

/-- Closures capture by value: every call starts from the closure's
creation-time copies, and assignments in a body write only that call's copies. -/
private def testValues (program : CheckedProgram) : IO Unit := do
  let pair : Value := .product (scalar 4) (scalar 5)
  for (name, expected) in [("named", scalar 3), ("returned", pair), ("shared", pair)] do
    let compiled ← compileNamed program name
    for _ in [0, 1] do
      require ((← compiled.run [scalar 2]) == expected)
        s!"{name}: capture, indirect call or cached entry reuse changed"
    compiled.checkResume [scalar 2] expected

/-- `loop` is assigned after the closure is created, so the closure's copy of
`loop` is uninitialized and its first recursive read fails, also after a
resumed checkpoint. -/
private def testSelfCell (program : CheckedProgram) : IO Unit := do
  let compiled ← compileNamed program "selfCell"
  let function ← match program.functions.find? (·.declaration == compiled.key.declaration) with
    | some function => pure function | none => throw (IO.userError "selfCell source function missing")
  let (node, binder) ← match function.typedBody.nodes.findSome? fun
      | .expression node@{ form := .reference "loop" (.local binder), .. } => some (node, binder)
      | _ => none with
    | some read => pure read | none => throw (IO.userError "selfCell closure-body read missing")
  let expected : SourceCoreFaultSites.Diagnostic := {
    error := .uninitializedLocal binder, site := .occurrence node.id.occurrence, span := some node.span }
  for _ in [0, 1] do
    let invocation ← compiled.invoke [scalar 2]
    match invocation.outcome with
    | .failed reason _ =>
        require (decide ((← invocation.diagnostic reason) = some expected))
          "selfCell: failure or cached entry reuse lost the uninitialized copy's read site"
    | _ => throw (IO.userError "selfCell: closure read of its uninitialized copy did not fail")
  let artifact ← compiled.execution.open
  let session ← boot artifact
  let (reason, failed) ← match ← get "complete selfCell invocation"
      (← session.run compiled.key [scalar 2] executionOptions) with
    | .failed reason failed => pure (reason, failed)
    | _ => throw (IO.userError "selfCell: complete invocation did not fail")
  let checkpoint ← match ← get "suspended selfCell invocation"
      (← session.run compiled.key [scalar 2] {executionOptions with executionFuel := 10}) with
    | .outOfFuel checkpoint => pure checkpoint
    | _ => throw (IO.userError "selfCell: small execution budget did not suspend")
  match ← checkpoint.resume 300000 1024 with
  | .failed resumedReason resumed =>
      require (resumedReason == reason && resumed.heapSize == failed.heapSize)
        "selfCell: resume changed the failure or allocated native world"
  | _ => throw (IO.userError "selfCell: resumed checkpoint did not fail")

private def testFailure (program : CheckedProgram) : IO Unit := do
  let compiled ← compileNamed program "failure"
  let function ← match program.functions.find? (·.declaration == compiled.key.declaration) with
    | some function => pure function | none => throw (IO.userError "failure source function missing")
  let reads := function.typedBody.nodes.filterMap fun
    | .expression node => match node.form with
      | .reference "f" (.local binder) => some (node, binder) | _ => none
    | _ => none
  let (node, binder) ← match reads with
    | [read] => pure read | _ => throw (IO.userError "failure occurrence missing")
  let invocation ← compiled.invoke []
  match invocation.outcome with
  | .failed reason _ =>
      require (decide ((← invocation.diagnostic reason) = some {
        error := .uninitializedLocal binder, site := .occurrence node.id.occurrence, span := some node.span }))
        "failed indirect callee lost its source occurrence"
  | _ => throw (IO.userError "uninitialized indirect callee did not fail")

def run : IO Unit := do
  let program ← get "function checking" (checkProgram workspace)
  testValues program
  testSelfCell program
  testFailure program
end Tests.SourceCompilerFunctions
end

section
-- leanmerge: from Solcore.Test.SourceCompilerIntegers
set_option autoImplicit false
namespace Tests.SourceCompilerIntegers
open Solcore Solcore.Frontend Tests.SourceCompilerFeatureSupport

private def operations : List (String × String × Bool) := [
  ("add", "+", false), ("sub", "-", false), ("mul", "*", false),
  ("div", "/", false), ("mod", "%", false),
  ("and", "&", false), ("or", "|", false), ("xor", "^", false),
  ("eq", "==", true), ("ne", "!=", true), ("lt", "<", true),
  ("le", "<=", true), ("gt", ">", true), ("ge", ">=", true)
]

private def workspaceText : String := String.intercalate "\n"
    ((operations.flatMap fun (name, operator, comparison) => [0, 5].map fun (right : Nat) =>
      "function op" ++ name ++ toString right ++ "(" ++ (if comparison then "comptime " else "") ++
        "left: integer) returns (" ++ (if comparison then "Bool" else "integer") ++
        ") { return left " ++ operator ++ " " ++ toString right ++ "; }") ++ [
      "function negate() returns (integer) { return ~5; }",
      "function callBuiltin(left: integer, right: integer) returns (integer) { return integerAdd(left, right); }",
      "function builtinValue(left: integer, right: integer) returns (integer) { let f: function(integer, integer) returns (integer) = integerSub; return f(left, right); }",
      "function intoWord(comptime left: integer) returns (Word) { return wordFromInteger(left); }",
      "function intoInteger(left: Word) returns (integer) { return wordToInteger(left); }",
      "function nativeLiteral() returns (integer) { return 1234567890123456789012345678901234567890; }",
      "function order(value: integer) returns (integer) {",
      " let step: function(integer) returns (integer) = lam(delta: integer) -> integer { value = integerAdd(value, delta); return value; };",
      " return integerSub(step(1), step(2)); }",
      "function recurse(value: integer) returns (integer) { return value == 0 ? 7 : recurse(value - 1); }",
      "function absent() returns (integer) { let value: integer; return value; }"
    ])

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := workspaceText }]
}


private def compile (program : CheckedProgram) (name : String) : IO Entry :=
  compileNamed program name [] {options with compilationFuel := 8192}
private def expect (entry : Entry) (arguments : List Value) (expected : Value) : IO Unit := do
  for _ in [0, 1] do
    require ((← entry.run arguments) == expected) "Integer result or cached entry reuse changed"

private def arithmetic (name : String) (left right : Int) : Value :=
  match name with
  | "add" => .integer (left + right)
  | "sub" => .integer (left - right)
  | "mul" => .integer (left * right)
  | "div" => .integer (Core.Integer.divide left right)
  | "mod" => .integer (Core.Integer.modulo left right)
  | "and" => .integer (Core.Integer.bitAnd left right)
  | "or" => .integer (Core.Integer.bitOr left right)
  | "xor" => .integer (Core.Integer.bitXor left right)
  | "eq" => .bool (left == right)
  | "ne" => .bool (left != right)
  | "lt" => .bool (left < right)
  | "le" => .bool (left ≤ right)
  | "gt" => .bool (left > right)
  | _ => .bool (left ≥ right)

def run : IO Unit := do
  let program ← get "Integer checking" (checkProgram workspace)
  let large : Int := Int.ofNat (2 ^ 300 + 19)
  for (name, _, _) in operations do
    for (right : Nat) in [0, 5] do
      let entry ← compile program ("op" ++ name ++ toString right)
      for left in [large, -17, 0] do
        expect entry [.integer left] (arithmetic name left (Int.ofNat right))
  expect (← compile program "negate") [] (.integer (~~~(5 : Int)))
  expect (← compile program "callBuiltin") [.integer large, .integer (-3)] (.integer (large - 3))
  expect (← compile program "builtinValue") [.integer large, .integer (-3)] (.integer (large + 3))
  expect (← compile program "intoWord") [.integer (-1)] (.word Core.Word.maximum)
  expect (← compile program "intoInteger") [.word Core.Word.maximum] (.integer (Int.ofNat Core.Word.maximum.val))
  expect (← compile program "nativeLiteral") [] (.integer 1234567890123456789012345678901234567890)
  /- Each call of `step` starts again from the captured `value`, so the result
  is `(large + 1) - (large + 2)` in either argument order. -/
  let order ← compile program "order"
  expect order [.integer large] (.integer (-1))
  order.checkResume [.integer large] (.integer (-1))
  expect (← compile program "recurse") [.integer 8] (.integer 7)
  let absent ← compile program "absent"
  let invocation ← absent.invoke []
  match invocation.outcome with
  | .failed reason _ => require ((← invocation.diagnostic reason).isSome) "Integer absence lost source diagnostic"
  | _ => throw (IO.userError "Integer absence did not fail")
  IO.println "public source Integer Core execution GREEN"
end Tests.SourceCompilerIntegers
end

section
-- leanmerge: from Solcore.Test.SourceCompilerLoops
/-! Public loop values/checkpoints and exact source allocation order use one
cached artifact. Internal native audits retain the generated cyclic loop cells. -/
set_option autoImplicit false
namespace Tests.SourceCompilerLoops
open Solcore Solcore.Frontend Tests.SourceCompilerFeatureSupport

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "function whileCount(start: Word) returns (Word, Word) {",
    "  let remaining: Word = start; let count: Word = 0;",
    "  while (remaining > 0) { remaining = remaining - 1; count = count + 1; }",
    "  return (remaining, count);",
    "}",
    "function forOrder(limit: Word) returns (Word, Word) {",
    "  let count: Word = 0;",
    "  for (let i: Word = 0; limit > i; i = i + 1) {",
    "    count = count + 1; if (i == 1) { continue; } count = count + 10;",
    "  } return (count, limit);",
    "}",
    "function forBreak(limit: Word) returns (Word) {",
    "  let i: Word = 17; for (let i: Word = 0; limit > i; i = i + 1) { break; } return i;",
    "}",
    "function nested() returns (Word) {",
    "  let count: Word = 0; for (let i: Word = 0; 2 > i; i = i + 1) {",
    "    for (let j: Word = 0; 2 > j; j = j + 1) { count = count + 1; }",
    "  } return count;",
    "}",
    "function absentCondition() returns (Word) { let missing: Bool; while (missing) { return 17; } return 0; }",
    "function absentPost() returns (Word) { let missing: Word; for (let i: Word = 0; true; i = missing) { continue; } return 0; }",
    "function absentInitializer() returns (Word) { let missing: Word; for (let i: Word = missing; true; i = i + 1) { break; } return 0; }",
    "function spin() { while (true) { continue; } }"
  ] }]
}

private def expectSuccess (entry : Entry) (arguments : List Value) (expected : Value)
    (cells : List Value) (type : Core.Ty) (loops : Nat) : IO Unit := do
  require ((← entry.run arguments) == expected) "public loop result changed"
  entry.checkCells arguments (cells.map fun value => (.word, some value))
  let complete ← entry.audit arguments
  let observed ← nativeObservation complete
  match observed with
  | .succeeded _ store => checkLoopCells store type loops
  | _ => throw (IO.userError "cached native loop did not finish")
  let pending ← entry.audit arguments 50
  match ← nativeObservation pending with
  | .outOfFuel _ => pure ()
  | _ => throw (IO.userError "native loop audit did not suspend")
  let resumed ← get "native loop resume" (pending.resume 300000)
  require ((← nativeObservation resumed) == observed)
    "loop resume changed its result or complete native store"
  entry.checkResume arguments expected 50

private def testExecution (program : CheckedProgram) : IO Unit := do
  let whileLoop ← compileNamed program "whileCount"
  expectSuccess whileLoop [scalar 3] (.product (scalar 0) (scalar 3))
    [scalar 3, scalar 0, scalar 3] (.product .word .word) 1
  let forLoop ← compileNamed program "forOrder"
  expectSuccess forLoop [scalar 3] (.product (scalar 23) (scalar 3))
    [scalar 3, scalar 23, scalar 3] (.product .word .word) 1
  expectSuccess forLoop [scalar 2] (.product (scalar 12) (scalar 2))
    [scalar 2, scalar 12, scalar 2] (.product .word .word) 1
  expectSuccess (← compileNamed program "forBreak") [scalar 3] (scalar 17)
    [scalar 3, scalar 17, scalar 0] .word 1
  expectSuccess (← compileNamed program "nested") [] (scalar 4)
    [scalar 4, scalar 2, scalar 2, scalar 2] .word 3

private def testFailures (program : CheckedProgram) : IO Unit := do
  for (name, loops) in ([("absentCondition", 1), ("absentPost", 1),
      ("absentInitializer", 0)] : List (String × Nat)) do
    let entry ← compileNamed program name
    let function ← match program.functions.find? (·.declaration == entry.key.declaration) with
      | some function => pure function
      | none => throw (IO.userError "loop declaration disappeared")
    let (node, binder) ← match function.typedBody.nodes.filterMap (fun
        | .expression node => match node.form with
          | .reference "missing" (.local binder) => some (node, binder)
          | _ => none
        | _ => none) with
      | [site] => pure site
      | _ => throw (IO.userError "loop failure lost its unique read occurrence")
    let invocation ← entry.invoke []
    match invocation.outcome with
    | .failed token _ =>
        require (token != Core.Word.zero && decide ((← invocation.diagnostic token) = some {
          error := .uninitializedLocal binder, site := .occurrence node.id.occurrence,
          span := some node.span })) "loop failure lost its exact source diagnostic"
    | _ => throw (IO.userError "loop did not report its failed read")
    let payload : TypeSystem.Ty := if name == "absentCondition" then .bool else .word
    entry.checkCells [] ([(payload, none)] ++
      if name == "absentPost" then [(.word, some (scalar 0))] else [])
    match ← nativeObservation (← entry.audit []) with
    | .failed _ store => checkLoopCells store .word loops
    | _ => throw (IO.userError "native loop failure changed")

private def testSuspension (program : CheckedProgram) : IO Unit := do
  let entry ← compileNamed program "spin"
  let invocation ← entry.invoke [] {executionOptions with executionFuel := 500}
  match invocation.outcome with
  | .outOfFuel checkpoint =>
      match ← checkpoint.resume 500 with
      | .outOfFuel _ => pure ()
      | _ => throw (IO.userError "resumed public spin unexpectedly finished")
  | _ => throw (IO.userError "public spin did not retain its checkpoint")

def run : IO Unit := do
  let program ← get "public loop checking" (checkProgram workspace)
  testExecution program
  testFailures program
  testSuspension program
end Tests.SourceCompilerLoops
end

section
-- leanmerge: from Solcore.Test.SourceCompilerRetainedBoundary
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.runTrusted

/-! Retained raw-value validation and inert-prefix audit. The public execution
facade uses owned values; these fixtures keep the old pure validator's exact
error ordering, and separately check that an authenticated inert source prefix
survives ordinary indexed Core execution. No source evaluator is imported. -/
set_option autoImplicit false
namespace Tests.SourceCompilerRetainedBoundary
open Solcore Solcore.Frontend SourceInference

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def plan (program : CheckedProgram) (seed : SourceCoreCompiler.Seed) :
    IO SourceSpecializationWorklist.Plan := do
  let request ← get "retained seed" (SourceProgramExecution.resolveSeed program seed)
  match ← get "retained worklist" (SourceSpecializationWorklist.run program [request] 128) with
  | .complete plan => pure plan
  | .budgetExhausted _ _ _ => throw (IO.userError "retained validator worklist exhausted")

/-- Called by the baseline compiler suite so it reuses the same checked source
and canonical seeds. This is not another public execution interface. -/
def run (program : CheckedProgram) (pairSeed directSeed blockedSeed dependentSeed : SourceCoreCompiler.Seed) : IO Unit := do
  let pairPlan ← plan program pairSeed
  let executable ← get "retained executable plan" (SourceCompilationPlan.prepareExecutablePlanEvidence program pairPlan)
  let compiled ← get "retained cached program" (SourceCoreCompiler.compileChecked program [pairSeed]
    {specializationBudget := 128, compilationFuel := 1000})
  let cached ← match compiled.artifact? with
    | some cached => pure cached | none => throw (IO.userError "retained fixture has no code")
  let key ← match cached.keys with
    | [key] => pure key | _ => throw (IO.userError "retained fixture roots changed")
  let root ← match cached.runtime.root? key with
    | some root => pure root | none => throw (IO.userError "retained runtime root missing")
  let pair : SourceTypedRuntime.Value := .product (.word (Core.Word.ofNatModulo 7)) (.word (Core.Word.ofNatModulo 8))
  let malformed : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (.bool true)⟩]}
  let retained : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (.word (Core.Word.ofNatModulo 99))⟩]}
  let openPrefix : SourceTypedRuntime.RuntimeState := {heap := ⟨.error, none⟩ :: retained.heap}
  require (!malformed.isDeeplySafe 128 program.signatures executable) "malformed cell passed pure deep validation"
  require (retained.isDeeplySafe 128 program.signatures executable && openPrefix.isDeeplySafe 128 program.signatures executable)
    "valid/inert uninitialized raw prefix failed pure validation"
  match SourceCoreUnifiedRuntime.boundaryFailure cached.runtime root [.bool true] 128 malformed with
  | some (.typeMismatch (.product .word .word) (some .bool)) => pure ()
  | _ => throw (IO.userError "raw input mismatch did not precede malformed initial heap")
  match SourceCoreUnifiedRuntime.boundaryFailure cached.runtime root [pair] 128 malformed with
  | some .deepSafetyInitialStateRejected => pure ()
  | _ => throw (IO.userError "malformed raw heap lost its pure boundary diagnostic")
  for budget in [0, 1] do
    match SourceCoreUnifiedRuntime.boundaryFailure cached.runtime root [pair] budget retained with
    | some (.inputValidationFuelExhausted (.product .word .word) actual) =>
        require (actual == budget) "nested raw validation lost its independent budget"
    | _ => throw (IO.userError "nested raw validation exhaustion changed precedence")
  require ((SourceCoreUnifiedRuntime.boundaryFailure cached.runtime root [pair] 128 retained).isNone)
    "valid retained inputs/heap failed validation"

  let recipe ← get "inert prefix recipe" (SourceCoreIndexedSession.Recipe.prepare cached)
  let artifact ← recipe.open
  require ((SourceCoreIndexedSession.InertPrefix.prepare artifact malformed 128).isNone)
    "malformed state acquired an inert-prefix receipt"
  let inert ← match SourceCoreIndexedSession.InertPrefix.prepare artifact openPrefix 128 with
    | some inert => pure inert | none => throw (IO.userError "valid inert prefix was rejected")
  let bootstrap ← artifact.bootstrap inert
  let pending ← match bootstrap.resume 0 with
    | .outOfFuel pending => pure pending | _ => throw (IO.userError "zero bootstrap fuel did not suspend")
  let session ← match pending.resume 300000 with
    | .ready session => pure session | _ => throw (IO.userError "inert-prefix bootstrap did not complete")
  require (reprStr session.inertPrefix == reprStr openPrefix) "bootstrap changed opaque source prefix"
  let checkpoint ← get "inert-prefix invocation" (session.start key
    [.product (.word (Core.Word.ofNatModulo 7)) (.word (Core.Word.ofNatModulo 8))] 128)
  let paused ← match ← checkpoint.resume 0 with
    | .outOfFuel paused => pure paused | _ => throw (IO.userError "zero execution fuel did not suspend")
  match ← paused.resume 300000 with
  | .succeeded completion =>
      require (completion.value == .word (Core.Word.ofNatModulo 12) &&
        reprStr completion.session.inertPrefix == reprStr openPrefix)
        "resumed native execution changed the value or inert source prefix"
  | _ => throw (IO.userError "retained prefix invocation did not finish")

  -- Arbitrary native stores remain a lower-level Core ABI capability, not a
  -- second public source invocation variant.
  let directPlan ← plan program directSeed
  let linked ← get "direct low-level Core link" (SourceCoreDirectLinking.linkWithStagingFuel program (.complete directPlan) 128)
  match linked.entries with
  | [entry] =>
      match entry.run? [.word (Core.Word.ofNatModulo 4)] 4096 [.bool true] with
      | some (.done (.word actual) [.bool true]) =>
          require (actual == Core.Word.ofNatModulo 8) "low-level supplied native store changed its result"
      | _ => throw (IO.userError "low-level Core ABI did not preserve its supplied store")
  | _ => throw (IO.userError "direct link changed root count")

  let blocked ← plan program blockedSeed
  match SourceCompilationPlan.validateExecutablePlanEvidence program blocked with
  | .error (.executableCoercionMethod _ _ _ (.missingTraitMethod _ "coerce")) => pure ()
  | _ => throw (IO.userError "missing coercion method lost its pure plan diagnostic")
  let dependent ← plan program dependentSeed
  match SourceCompilationPlan.validateExecutablePlanEvidence program dependent with
  | .error (.stagedExpressionType _ .integer) => pure ()
  | _ => throw (IO.userError "dependent staged Integer lost its pure plan rejection")
end Tests.SourceCompilerRetainedBoundary
end

section
-- leanmerge: from Solcore.Test.SourceCompiler
#check_failure Solcore.Frontend.SourceCoreExecution.Options.backendPreference
#check_failure Solcore.Frontend.SourceCoreExecution.Backend
#check_failure Solcore.Frontend.SourceCoreExecution.Invocation
#check_failure Solcore.Frontend.SourceCoreExecution.Compiled.backend
#check_failure Solcore.Frontend.SourceCoreExecution.Session.runCore
#check_failure Solcore.Frontend.SourceCoreExecution.Session.runTyped
#check_failure Solcore.Frontend.SourceCoreExecution.Value.closure
#check_failure Solcore.Frontend.SourceCoreExecution.Value.cellRef
#check_failure Solcore.Frontend.SourceCoreExecution.Session.state
#check_failure Solcore.Frontend.SourceCoreExecution.Session.store
#check_failure Solcore.Frontend.SourceCoreExecution.Checkpoint.state
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! The public source compiler has one Core/value/session boundary. Root
metadata, source behavior, ABI discovery and validation are preserved; there is
no backend choice or native/source invocation mismatch in this API. -/
set_option autoImplicit false
namespace Tests.SourceCompiler
open Solcore Solcore.Frontend Solcore.TypeSystem SourceCoreExecution
private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def scalar (value : Nat) : Value := .word (word value)
private def moduleId (path : String) : IO Workspace.ModuleId := do
  match Workspace.CanonicalSourcePath.parse path with
  | none => throw (IO.userError s!"invalid test module path `{path}`")
  | some canonical => pure { library := .main, path := canonical.modulePath }
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [
    {
      path := "main.solc"
      content := String.intercalate "\n" [
        "import {Ticket, WordTicket} from provider;",
        "function direct(value: Word) returns (Word) { return value * 2; }",
        "function recurse(value: Word) returns (Word) { return value == 0 ? 31 : recurse(value - 1); }",
        "function visibleAlias(value: (Word, Word)) returns (Word) {",
        "  let ticket: WordTicket = .Open(7);",
        "  match (ticket) {",
        "    case .Open(inner) {",
        "      let result: Word = inner;",
        "      result += 5;",
        "      return result;",
        "    }",
        "    default { return 0; }",
        "  }",
        "}",
        "function globalIdentity<T>(value: T) returns (T) { return value; }",
        "trait Eq<T> {}",
        "impl Eq<Word> {}",
        "trait Coerce<From, To> {",
        "  function coerce(value: From) returns (To);",
        "}",
        "function coercionSeed(value: Bool) returns (Word) {",
        "  return value ? 40 : 6;",
        "}",
        "impl Coerce<Bool, Word> {",
        "  function coerce(value: Bool) returns (Word) {",
        "    let scratch: mapping(Word => Word);",
        "    scratch[0] = coercionSeed(value);",
        "    scratch[0] += 2;",
        "    return scratch[0];",
        "  }",
        "}",
        "type WordFunction = function(Word) returns (Word);",
        "function returnedIdentity(value: Word) returns (Word) { return value; }",
        "impl Coerce<Word, WordFunction> {",
        "  function coerce(value: Word) returns (WordFunction) {",
        "    return returnedIdentity;",
        "  }",
        "}",
        "function functionFromCoercion(value: Word) returns (WordFunction) {",
        "  return value;",
        "}",
        "function keepAs<T, U>(guard: T, value: U) returns (U) where T: Eq { return value; }",
        "function localProof(flag: Bool) returns (Word, Bool) {",
        "  let f = lam(value) { return keepAs(1, value); };",
        "  return (f(2), f(flag));",
        "}",
        "function keep<T>(value: T) returns (T) where T: Eq { return value; }",
        "function relay<T>(value: T) returns (T) where T: Eq { return keep(value); }",
        "function typedEvidence(value: Word) returns (Word) {",
        "  let table: mapping(Word => Word);",
        "  table[0] = relay(value);",
        "  return table[0];",
        "}",
        "function typedCoercion(value: Bool) returns (Word) {",
        "  let table: mapping(Word => Word);",
        "  table[0] = value;",
        "  return table[0];",
        "}",
        "function polymorphicLocal(flag: Bool) returns (Word, Bool) {",
        "  let id = lam(value) { return globalIdentity(value); };",
        "  return (id(11), id(flag));",
        "}",
        "function nestedPolymorphicLocal(flag: Bool) returns (Word, Bool) {",
        "  let outer = lam(value) {",
        "    let inner = lam(innerValue) { return globalIdentity(innerValue); };",
        "    return inner(value);",
        "  };",
        "  return (outer(13), outer(flag));",
        "}",
        "function recursiveContextPolymorphicLocal(flag: Bool) returns (Word, Bool) {",
        "  let outer = lam(value) {",
        "    let middle = lam(item) {",
        "      let inner = lam(innerValue) { return globalIdentity(innerValue); };",
        "      return inner(item);",
        "    };",
        "    return middle(value);",
        "  };",
        "  return (outer(15), outer(flag));",
        "}"
      ]
    },
    {
      path := "provider.solc"
      content := String.intercalate "\n" [
        "enum Ticket<T> { Open(T), Closed }",
        "type WordTicket = Ticket<Word>;",
        "export {Ticket(Open), WordTicket};"
      ]
    },
    {
      path := "blocked.solc"
      content := String.intercalate "\n" [
        "trait Coerce<From, To> {}",
        "enum Box { Only }",
        "impl Coerce<Word, Box> {}",
        "function accept(value: Box) returns (Box) { return value; }",
        "function blockedHelper(value: Word) returns (Box) { return accept(value); }",
        "function blocked(value: Word) returns (Box) { return blockedHelper(value); }",
        "trait Marker<T> {}",
        "impl Marker<Word> {}",
        "function constrained(value: Word) returns (Word) where Word: Marker {",
        "  let table: mapping(Word => Word);",
        "  table[0] = value;",
        "  return table[0];",
        "}",
        "function staged(comptime value: Word) returns (Word) { return value; }",
        "type StagedWord = comptime<Word>;",
        "type PairWithStage = (Word, StagedWord);",
        "type DeepStage = (StagedWord, (Word, StagedWord));",
        "function stagedType(value: StagedWord) returns (Word) { return 1; }",
        "function integerResult() returns (integer) { return 1; }",
        "function nestedStaged(value: PairWithStage) returns (Word) { return 1; }",
        "function dependent(flag: Bool) returns (Word) { return wordFromInteger(flag ? 1 : 2); }",
        "function nestedComptime(value: DeepStage) returns (DeepStage) { return value; }",
        "function integerBitAnd() returns (integer) { return 5 & 3; }",
        "function integerBitXor() returns (integer) { return 5 ^ 3; }",
        "function integerBitOr() returns (integer) { return 5 | 3; }",
        "function integerBitNot() returns (integer) { return ~5; }",
        "function markedEffects(comptime seed: Word) returns (comptime<Word>) {",
        "  let total: Word = seed;",
        "  let table: mapping(Word => Word);",
        "  let bump = lam(comptime delta: Word) -> Word {",
        "    total += delta;",
        "    table[0] = total;",
        "    return table[0];",
        "  };",
        "  return bump(3);",
        "}",
        "function markedEffectsEntry() returns (Word) {",
        "  return markedEffects(9);",
        "}"
      ]
    }
  ]
  externalLibraries := []
}

/-- A compact raw-workspace fixture for automatic entry discovery, exported
ABI discovery, re-export aliases, and shared-graph multi-root compilation. -/
private def orchestrationWorkspace : Workspace.RawWorkspace := {
  entry := "api.solc"
  mainSources := [
    {
      path := "api.solc"
      content := String.intercalate "\n" [
        "import {twice as doubled, recursive} from provider;",
        "function main() returns (Word) { return 17; }",
        "function local(value: Word) returns (Word) { return value + 1; }",
        "function hidden(value: Word) returns (Word) { return value; }",
        "export {doubled, local, recursive};"
      ]
    },
    {
      path := "provider.solc"
      content := String.intercalate "\n" [
        "function twice(value: Word) returns (Word) { return value * 2; }",
        "function recursive(value: Word) returns (Word) {",
        "  return value == 0 ? 31 : recursive(value - 1);",
        "}",
        "function providerOnly(value: Word) returns (Word) { return value; }",
        "export {twice, recursive, providerOnly};"
      ]
    }
  ]
  externalLibraries := []
}
private def compilerOptions : Options :=
  { specializationBudget := 128, compilationFuel := 1000 }
private def runtimeOptions : RunOptions :=
  { inputValidationFuel := 128, executionFuel := 300000, outputValidationFuel := 128 }
private def boot (artifact : Artifact) : IO (Session artifact) := do
  let bootstrap ← artifact.bootstrap
  match bootstrap.resume 300000 with
  | .ready session => pure session
  | .error error => throw (IO.userError s!"compiler bootstrap rejected: {reprStr error}")
  | .outOfFuel _ => throw (IO.userError "compiler bootstrap exhausted")
private def execute {artifact : Artifact} (session : Session artifact) (key : Key) (arguments : List Value) :
    IO (Completion artifact) := do
  match ← session.run key arguments runtimeOptions with
  | .ok (.succeeded completion) => pure completion
  | .error error => throw (IO.userError s!"public inputs rejected: {reprStr error}")
  | .ok (.exportError error _) => throw (IO.userError s!"public output rejected: {reprStr error}")
  | .ok (.failed token _) => throw (IO.userError s!"unexpected language failure: {reprStr token}")
  | .ok (.outOfFuel _) => throw (IO.userError "public execution exhausted")
private structure Entry where
  compiled : Compiled
  root : SourceCoreCompiler.Root compiled.plan
private def Entry.key (entry : Entry) : Key := entry.root.key
private def Entry.inputTypes (entry : Entry) : List Ty := entry.root.inputTypes
private def Entry.resultType (entry : Entry) : Ty := entry.root.resultType
private def entry (compiled : Compiled) (index : Nat := 0) : IO Entry :=
  match compiled.root? index with
  | some root => pure ⟨compiled, root⟩
  | none => throw (IO.userError s!"compiled root missing at {index}")
private def compileNamed (program : CheckedProgram) (path name : String) : IO Entry := do
  let selectedModule ← moduleId path
  entry (← get s!"compile {path}.{name}" (compileChecked program [SourceCoreCompiler.Seed.named selectedModule name] compilerOptions))
private def Entry.run (entry : Entry) (arguments : List Value) : IO Value := do
  let artifact ← entry.compiled.open
  let session ← boot artifact
  pure (← execute session entry.key arguments).value
private def expectWord (label : String) (expected : Nat) (actual : IO Value) : IO Unit := do
  assertTrue ((← actual) == scalar expected) s!"{label} returned the wrong Word"

private structure PreparedSet where
  checked : CheckedProgram
  direct : Entry
  recursive : Entry
  pair : Entry

private def testCheckedReuse : IO PreparedSet := do
  let checked ← get "compiler checking" (checkProgram workspace)
  let direct ← compileNamed checked "main.solc" "direct"
  let recursive ← compileNamed checked "main.solc" "recurse"
  let pair ← compileNamed checked "main.solc" "visibleAlias"
  let main ← moduleId "main.solc"
  assertTrue (decide (direct.key.declaration.moduleId = main ∧ recursive.key.declaration.moduleId = main ∧
      pair.key.declaration.moduleId = main ∧ direct.key.arguments = [] ∧ recursive.key.arguments = [] ∧ pair.key.arguments = []))
    "compiled roots lost canonical module or ground arguments"
  assertTrue (decide (direct.inputTypes = [.word] ∧ direct.resultType = .word ∧
      recursive.inputTypes = [.word] ∧ recursive.resultType = .word ∧
      pair.inputTypes = [.product .word .word] ∧ pair.resultType = .word))
    "compiled roots lost source signature metadata"
  assertTrue (direct.compiled.plan.specializations.length == 1 && recursive.compiled.plan.specializations.length == 1 &&
    pair.compiled.plan.specializations.length == 1) "single-function plan gained specializations"
  let artifact ← direct.compiled.open
  let session ← boot artifact
  let first ← execute session direct.key [scalar 7]
  let second ← execute first.session direct.key [scalar 9]
  assertTrue (first.value == scalar 14 && second.value == scalar 18)
    "reusing one cached artifact/session changed direct results"
  expectWord "recursive source root" 31 (recursive.run [scalar 3])
  expectWord "imported nominal alias" 12 (pair.run [.product (scalar 7) (scalar 8)])
  for (name, expected) in [("polymorphicLocal", 11), ("nestedPolymorphicLocal", 13), ("recursiveContextPolymorphicLocal", 15)] do
    let compiled ← compileNamed checked "main.solc" name
    assertTrue (compiled.compiled.plan.specializations.length == 3) s!"{name}: local generic instances changed"
    let edges := compiled.compiled.plan.callEdges.filter (fun edge => decide (edge.caller = compiled.key))
    assertTrue (compiled.compiled.plan.callEdges.length == 2 && edges.length == 2 &&
      (edges.map (·.occurrence)).eraseDups.length == 1 &&
      (edges.map (·.callee.arguments)).contains [.word] && (edges.map (·.callee.arguments)).contains [.bool])
      s!"{name}: contextual Word/Bool calls disappeared"
    assertTrue ((← compiled.run [.bool true]) == .product (scalar expected) (.bool true))
      s!"{name}: local instantiation result changed"
  let proof ← compileNamed checked "main.solc" "localProof"
  assertTrue (proof.compiled.plan.specializations.length == 3 &&
    (← proof.run [.bool true]) == .product (scalar 2) (.bool true)) "local evidence specialization changed"
  let evidence ← compileNamed checked "main.solc" "typedEvidence"
  assertTrue (evidence.compiled.plan.specializations.length == 3) "evidence frontier lost root/relay/callee"
  expectWord "evidence forwarding" 73 (evidence.run [scalar 73])
  let coercion ← compileNamed checked "main.solc" "typedCoercion"
  expectWord "stateful coercion true" 42 (coercion.run [.bool true])
  expectWord "stateful coercion false" 8 (coercion.run [.bool false])
  let returned ← compileNamed checked "main.solc" "functionFromCoercion"
  match ← returned.run [scalar 1] with
  | .function handle => assertTrue (handle.sourceType == .function .word .word) "coercion lost returned function type"
  | _ => throw (IO.userError "method-discovered function was not exported as an owned handle")
  pure ⟨checked, direct, recursive, pair⟩

private def testInputBoundary (prepared : PreparedSet) : IO Unit := do
  let artifact ← prepared.pair.compiled.open
  let session ← boot artifact
  match session.start prepared.pair.key [.bool true] 128 with
  | .error {code := .compatible {code := .sourceTypeMismatch (.product .word .word) .bool, ..}, ..} => pure ()
  | _ => throw (IO.userError "public value mismatch lost exact expected/actual types")
  let pair : Value := .product (scalar 7) (scalar 8)
  for fuel in [0, 1] do
    match session.start prepared.pair.key [pair] fuel with
    | .error {code := .compatible {code := .exhausted, ..}, ..} => pure ()
    | _ => throw (IO.userError "public deep input validation ignored its budget")
  match session.start prepared.pair.key [] 128 with
  | .error {code := .argumentCountMismatch 1 0, ..} => pure ()
  | _ => throw (IO.userError "public input arity mismatch was accepted")
  let checkpoint ← get "public typed checkpoint" (session.start prepared.pair.key [pair] 128)
  let paused ← match ← checkpoint.resume 0 128 with
    | .outOfFuel paused => pure paused | _ => throw (IO.userError "execution fuel was not independent of validation")
  match ← paused.resume 300000 128 with
  | .succeeded completion => assertTrue (completion.value == scalar 12) "resume changed nominal source result"
  | _ => throw (IO.userError "validated public checkpoint failed to resume")
  -- Rejection never changes the caller's persistent session.
  assertTrue ((← execute session prepared.pair.key [pair]).value == scalar 12)
    "input rejection changed reusable session state"

private def testCapabilities (checked : CheckedProgram) : IO Unit := do
  let cases : List (String × List Ty × Ty × List Value × Value) := [
      ("constrained", [.word], .word, [scalar 19], scalar 19),
      ("staged", [.word], .word, [scalar 23], scalar 23),
      ("stagedType", [.comptime .word], .word, [scalar 29], scalar 1),
      ("integerResult", [], .integer, [], .integer 1),
      ("nestedStaged", [.product .word (.comptime .word)], .word, [.product (scalar 2) (scalar 3)], scalar 1),
      ("nestedComptime", [.product (.comptime .word) (.product .word (.comptime .word))],
        .product (.comptime .word) (.product .word (.comptime .word)),
        [.product (scalar 4) (.product (scalar 5) (scalar 6))], .product (scalar 4) (.product (scalar 5) (scalar 6))),
      ("integerBitAnd", [], .integer, [], .integer 1),
      ("integerBitXor", [], .integer, [], .integer 6),
      ("integerBitOr", [], .integer, [], .integer 7),
      ("integerBitNot", [], .integer, [], .integer (-6)),
      ("markedEffects", [.word], .word, [scalar 9], scalar 12),
      ("markedEffectsEntry", [], .word, [], scalar 12)]
  for (name, inputTypes, resultType, arguments, expected) in cases do
    let compiled ← compileNamed checked "blocked.solc" name
    assertTrue (compiled.inputTypes == inputTypes && compiled.resultType == resultType)
      s!"{name}: raw public source signature metadata changed"
    assertTrue ((← compiled.run arguments) == expected) s!"{name}: staged/evidence/Integer behavior changed"

private def testCompilationErrors (checked : CheckedProgram) : IO Unit := do
  let main ← moduleId "main.solc"
  let missing := SourceCoreCompiler.Seed.named main "missing"
  match compileChecked checked [missing] compilerOptions with
  | .error (.compilation (.seed 0 actual (.unknownName owner "missing"))) =>
      assertTrue (decide (actual = missing ∧ owner = main)) "seed rejection lost its original request"
  | _ => throw (IO.userError "unknown public root did not report its seed error")
  match compileChecked checked [SourceCoreCompiler.Seed.named main "direct"]
      {compilerOptions with specializationBudget := 0} with
  | .error (.compilation (.specializationBudgetExhausted next pending)) =>
      assertTrue (next.declaration.moduleId == main && pending > 0) "shared specialization budget lost its frontier"
  | _ => throw (IO.userError "zero shared specialization budget was accepted")
  let blocked ← moduleId "blocked.solc"
  match compileChecked checked [SourceCoreCompiler.Seed.named blocked "blocked"] compilerOptions with
  | .error (.compilation (.planEvidence (.executableCoercionMethod _ _ _ (.missingTraitMethod _ "coerce")))) => pure ()
  | _ => throw (IO.userError "unavailable coercion method escaped the one compiler's plan validation")
  match compileChecked checked [SourceCoreCompiler.Seed.named blocked "dependent"] compilerOptions with
  | .error (.compilation (.planEvidence (.stagedExpressionType _ .integer))) => pure ()
  | _ => throw (IO.userError "dependent staged Integer escaped plan validation")
  let invalid : Workspace.RawWorkspace := {
    entry := "broken.solc", externalLibraries := [],
    mainSources := [{path := "broken.solc", content := "function broken(value: Word returns (Word) { return value; }"}] }
  match compile invalid [SourceCoreCompiler.Seed.named (← moduleId "broken.solc") "broken"] compilerOptions with
  | .error (.compilation (.checking (_ :: _))) => pure ()
  | _ => throw (IO.userError "malformed source escaped checking precedence")
  match compile invalid [] compilerOptions with
  | .error (.compilation (.checking (_ :: _))) => pure ()
  | _ => throw (IO.userError "empty roots bypassed raw source checking")

private def abiRootNamed (abi : StaticWordProgram) (name : String) : IO (StaticWordRoot abi.compiled) :=
  match abi.roots.find? (fun root => root.metadata.name.text == name) with
  | some root => pure root
  | none => throw (IO.userError s!"missing compiled ABI root {name}")

/-- Roots share one graph budget; public order and duplicates remain observable.
ABI discovery still uses exported source names and canonical declarations. -/
private def testProgramOrchestration : IO Unit := do
  let api ← moduleId "api.solc"
  let provider ← moduleId "provider.solc"
  let main ← entry (← get "conventional main" (compileEntry orchestrationWorkspace compilerOptions))
  assertTrue (main.inputTypes.isEmpty && main.resultType == .word && main.key.declaration.moduleId == api)
    "main discovery lost its entry module or signature"
  expectWord "conventional workspace main" 17 (main.run [])
  let checked ← get "orchestration checking" (checkProgram orchestrationWorkspace)
  let requested := [SourceCoreCompiler.Seed.named provider "twice", .named provider "recursive", .named provider "twice"]
  let many ← get "checked shared roots" (compileChecked checked requested compilerOptions)
  match many.roots with
  | [first, second, third] =>
      assertTrue (many.rootCount == 3 && first.key == third.key && first.key != second.key &&
        decide (many.roots.map (·.seed) = requested)) "root order or duplicate requests changed"
  | _ => throw (IO.userError "shared compilation changed root count")
  match compileChecked checked [SourceCoreCompiler.Seed.named provider "twice", .named provider "missing"] compilerOptions with
  | .error (.compilation (.seed 1 actual (.unknownName owner "missing"))) =>
      assertTrue (decide (actual = SourceCoreCompiler.Seed.named provider "missing" ∧ owner = provider))
        "missing second root lost request position or metadata"
  | _ => throw (IO.userError "missing second root changed its seed diagnostic")
  let rawMany ← get "raw shared roots" (compile orchestrationWorkspace requested compilerOptions)
  assertTrue (rawMany.keys == many.keys) "raw compilation changed ordered canonical roots"
  let one : Options := {compilerOptions with specializationBudget := 1}
  match compileChecked checked [SourceCoreCompiler.Seed.named provider "twice", .named api "local"] one with
  | .error (.compilation (.specializationBudgetExhausted _ pending)) =>
      assertTrue (pending > 0) "shared budget failure lost the unfinished frontier"
  | _ => throw (IO.userError "two distinct roots incorrectly received independent graph budgets")
  let duplicate ← get "duplicate root shared budget" (compileChecked checked
    [SourceCoreCompiler.Seed.named provider "twice", .named provider "twice"] one)
  assertTrue (duplicate.rootCount == 2 && duplicate.plan.specializations.length == 1)
    "duplicate requests consumed separate specialization budgets"

  let abi ← get "Static Word roots" (compileStaticWord orchestrationWorkspace compilerOptions)
  assertTrue (abi.count == 3) "ABI discovery lost an exported root"
  let doubled ← abiRootNamed abi "doubled"
  let localRoot ← abiRootNamed abi "local"
  let recursive ← abiRootNamed abi "recursive"
  assertTrue (doubled.root.key.declaration.moduleId == provider &&
    localRoot.root.key.declaration.moduleId == api && recursive.root.key.declaration.moduleId == provider &&
    (abi.roots.find? (fun root => root.metadata.name.text == "hidden")).isNone &&
    (abi.roots.find? (fun root => root.metadata.name.text == "providerOnly")).isNone)
    "ABI alias/module/export filtering changed"
  let discovered ← get "independent ABI discovery" (SourceCoreRootDiscovery.discoverStaticWordRoots checked api)
  assertTrue (abi.roots.map (·.metadata.name.text) == discovered.map (·.metadata.name.text))
    "compilation reordered discovered ABI roots"
  match abi.rootForSelector? doubled.metadata.selector with
  | some selected => assertTrue (selected.metadata.name.text == "doubled") "selector lookup chose another root"
  | none => throw (IO.userError "selector lookup lost an admitted root")
  let artifact ← abi.compiled.open
  let session ← boot artifact
  let first ← execute session doubled.root.key [scalar 7]
  let second ← execute first.session localRoot.root.key [scalar 7]
  let third ← execute second.session recursive.root.key [scalar 3]
  assertTrue (first.value == scalar 14 && second.value == scalar 8 && third.value == scalar 31)
    "ABI alias/local/recursive results changed in the shared session"
  let missingMain : Workspace.RawWorkspace := {
    entry := "missing.solc"
    mainSources := [{
      path := "missing.solc"
      content := "function helper() returns (Word) { return 0; }"
    }]
    externalLibraries := []
  }
  let missingModule ← moduleId "missing.solc"
  match compileEntry missingMain with
  | .error (.compilation (.seed 0 _ (.unknownName actual "main"))) =>
      assertTrue (actual == missingModule)
        "automatic entry failure lost its canonical module"
  | .error error => throw (IO.userError
      s!"missing main changed diagnostic: {reprStr error}")
  | .ok _ => throw (IO.userError "workspace without main compiled as an entry")

  let invalidAbi : Workspace.RawWorkspace := {
    entry := "bad.solc"
    mainSources := [{
      path := "bad.solc"
      content := String.intercalate "\n" [
        "function bad(value: Bool) returns (Word) { return value ? 1 : 0; }",
        "export {bad};"
      ]
    }]
    externalLibraries := []
  }
  match compileStaticWord invalidAbi with
  | .error (.discovery (.unsupportedParameters _ "bad" [.bool] [false])) =>
      pure ()
  | .error error => throw (IO.userError
      s!"unsupported ABI signature changed diagnostic: {reprStr error}")
  | .ok _ => throw (IO.userError
      "unsupported Bool ABI parameter was silently accepted")

  let duplicateAbi : Workspace.RawWorkspace := {
    entry := "duplicate.solc"
    mainSources := [{
      path := "duplicate.solc"
      content := String.intercalate "\n" [
        "function same(value: Word) returns (Word) { return value; }",
        "function same(value: Word) returns (Word) { return value + 1; }",
        "export {same};"
      ]
    }]
    externalLibraries := []
  }
  match compileStaticWord duplicateAbi with
  | .error (.discovery
      (.duplicateSignature "same" "same" "same(uint256)")) => pure ()
  | .error error => throw (IO.userError
      s!"duplicate ABI signature changed diagnostic: {reprStr error}")
  | .ok _ => throw (IO.userError
      "duplicate ABI signatures were silently accepted")

  let collisionAbi : Workspace.RawWorkspace := {
    entry := "collision.solc"
    mainSources := [{
      path := "collision.solc"
      content := String.intercalate "\n" [
        "function f116643(value: Word) returns (Word) { return value; }",
        "function f38491(value: Word) returns (Word) { return value; }",
        "export {f38491, f116643};"
      ]
    }]
    externalLibraries := []
  }
  match compileStaticWord collisionAbi with
  | .error (.discovery (.selectorCollision
      "f116643" "f38491" "f116643(uint256)" "f38491(uint256)" selector)) =>
      assertTrue (selector.toUInt32.toNat == 0x77dbd42e)
        "ABI collision diagnostic lost its canonical selector"
  | .error error => throw (IO.userError
      s!"ABI selector collision changed diagnostic: {reprStr error}")
  | .ok _ => throw (IO.userError
      "colliding ABI selectors were silently accepted")

/-- Checking, graph preparation, bootstrap, input validation and execution use
separate budgets. Suspension retains an opaque, reusable checkpoint. -/
private def testOneShotLimits : IO Unit := do
  let main ← moduleId "main.solc"
  let compiled ← get "limited raw preparation" (compile workspace [SourceCoreCompiler.Seed.named main "visibleAlias"]
    {checkingFuel := 1024, specializationBudget := 32, compilationFuel := 128})
  let root ← entry compiled
  let artifact ← compiled.open
  let bootstrap ← artifact.bootstrap
  let bootstrap ← match bootstrap.resume 0 with
    | .outOfFuel checkpoint => pure checkpoint
    | _ => throw (IO.userError "zero bootstrap budget failed to suspend")
  let session ← match bootstrap.resume 300000 with
    | .ready session => pure session
    | _ => throw (IO.userError "bootstrap did not resume")
  match ← session.run root.key [.product (scalar 7) (scalar 8)]
      {inputValidationFuel := 64, executionFuel := 1, outputValidationFuel := 128} with
  | .ok (.outOfFuel checkpoint) =>
      match ← checkpoint.resume 300000 128 with
      | .succeeded done => assertTrue (done.value == scalar 12) "limited invocation changed resumed result"
      | _ => throw (IO.userError "limited invocation did not resume")
  | _ => throw (IO.userError "execution budget was conflated with validation or preparation")

/-- Durable runtime, root, ABI, evidence, staging and boundary regressions use
one compiler and one owned-value session API. -/
def testSourceCompiler : IO Unit := do
  let prepared ← testCheckedReuse
  testProgramOrchestration
  testInputBoundary prepared
  testOneShotLimits
  testCapabilities prepared.checked
  testCompilationErrors prepared.checked
  let main ← moduleId "main.solc"
  let blocked ← moduleId "blocked.solc"
  SourceCompilerRetainedBoundary.run prepared.checked
    (SourceCoreCompiler.Seed.named main "visibleAlias") (SourceCoreCompiler.Seed.named main "direct")
    (SourceCoreCompiler.Seed.named blocked "blocked") (SourceCoreCompiler.Seed.named blocked "dependent")
  IO.println "public source compiler integration GREEN"
end Tests.SourceCompiler
end

section
-- leanmerge: from Solcore.Test.SourceCompilerSession
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.RuntimeValue
#check_failure Solcore.Frontend.SourceCoreExecution.Compiled.mk
#check_failure Solcore.Frontend.SourceCoreExecution.Compiled.recipe
#check_failure Solcore.Frontend.SourceCoreExecution.Handle.mk
#check_failure Solcore.Frontend.SourceCoreExecution.Options.backendPreference
#check_failure Solcore.Frontend.SourceCoreExecution.Value.closure
#check_failure Solcore.Frontend.SourceCoreExecution.Value.cellRef

/-! Explicit roots share one checked catalog and cached ownership recipe.
These tests exercise native session reuse; importing an arbitrary pre-existing
source heap or source closure remains outside this boundary. -/

set_option autoImplicit false

namespace Tests.SourceCompilerSession

open Solcore Solcore.Frontend SourceCoreExecution
abbrev OwnedValue := SourceCoreExecution.Value

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def word (value : Nat) : OwnedValue := .word (Core.Word.ofNatModulo value)
private def functionType : TypeSystem.Ty := .function .word .word

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "enum Holder { Put(function(Word) returns (Word)) }",
    "function inc(value: Word) returns (Word) { return value + 1; }",
    "function makeAdder(value: Word) returns (function(Word) returns (Word)) {",
    " return lam(delta: Word) -> Word { value = value + delta; return inc(value); }; }",
    "function use(f: function(Word) returns (Word), delta: Word) returns (Word) { return f(delta); }",
    "function mirror(f: function(Word) returns (Word)) returns (function(Word) returns (Word)) { return f; }",
    "function box(f: function(Word) returns (Word)) returns (Holder) { return .Put(f); }",
    "function unbox(value: Holder) returns (function(Word) returns (Word)) { match (value) { case .Put(f) { return f; } } }",
    "function keep<T>(value: T) returns (T) { return value; }"
  ] }] }

private def signature (program : CheckedProgram) (name : String) : IO ProgramFunctionSignature :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure signature
  | _ => throw (IO.userError s!"multi-root fixture function missing: {name}")

private def root (compiled : Compiled) (index : Nat) : IO (SourceCoreCompiler.Root compiled.plan) :=
  match compiled.root? index with
  | some root => pure root
  | none => throw (IO.userError s!"multi-root metadata missing: {index}")

private def execute {artifact : Artifact} (session : Session artifact)
    (key : Key) (arguments : List OwnedValue) : IO (Completion artifact) := do
  match ← session.run key arguments {executionFuel := 65536} with
  | .ok (.succeeded completion) => pure completion
  | .error error => throw (IO.userError s!"multi-root session input rejected: {reprStr error}")
  | .ok (.exportError error _) => throw (IO.userError s!"multi-root result rejected: {reprStr error}")
  | _ => throw (IO.userError "multi-root session did not finish successfully")

private def boot (artifact : Artifact) : IO (Session artifact) := do
  let bootstrap ← artifact.bootstrap
  match bootstrap.resume 300000 with
  | .ready session => pure session
  | .error error => throw (IO.userError s!"shared bootstrap rejected: {reprStr error}")
  | .outOfFuel _ => throw (IO.userError "shared bootstrap exhausted")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"multi-root source rejected: {reprStr error}")
  let moduleId : Workspace.ModuleId ← match Workspace.CanonicalSourcePath.parse "main.solc" with
    | some canonical => pure { library := .main, path := canonical.modulePath }
    | none => throw (IO.userError "multi-root module identity failed")
  let use ← signature program "use"
  let seeds := [SourceCoreCompiler.Seed.named moduleId "makeAdder", .declaration use.id, .named moduleId "mirror",
    .named moduleId "box", .named moduleId "unbox", .named moduleId "keep" [.word],
    .named moduleId "keep" [.bool], .named moduleId "use"]
  let options : Options := { specializationBudget := 256, compilationFuel := 256 }
  let compiled ← match compileChecked program seeds options with
    | .ok compiled => pure compiled
    | .error error => throw (IO.userError s!"multi-root preparation rejected: {reprStr error}")
  assertTrue (compiled.rootCount == seeds.length && compiled.keys.length == seeds.length)
    "explicit roots were deduplicated or reordered"
  assertTrue (compiled.root? seeds.length |>.isNone) "out-of-range root metadata was accepted"
  for (seed, index) in seeds.zipIdx do
    assertTrue (decide ((← root compiled index).seed = seed)) "public root order changed"
  let maker ← root compiled 0
  let consumer ← root compiled 1
  let mirror ← root compiled 2
  let box ← root compiled 3
  let unbox ← root compiled 4
  let keepWord ← root compiled 5
  let keepBool ← root compiled 6
  let duplicate ← root compiled 7
  assertTrue (consumer.key == duplicate.key) "named/declaration roots failed canonicalization"
  assertTrue (keepWord.key != keepBool.key) "distinct generic roots shared a specialization key"
  assertTrue (decide (maker.inputTypes = [.word] ∧ maker.resultType = functionType ∧
    consumer.inputTypes = [functionType, .word] ∧ consumer.resultType = .word ∧
    keepWord.inputTypes = [.word] ∧ keepBool.resultType = .bool))
    "ordered root metadata lost closed source signatures"
  assertTrue (compiled.program.signatures.functions.map (·.name) == program.signatures.functions.map (·.name))
    "cached facade lost its source signature catalog"
  assertTrue (!compiled.program.signatures.dataTypes.isEmpty)
    "all roots lost the actual source nominal catalog"
  let rawCompiled ← match compile workspace seeds options with
    | .ok compiled => pure compiled
    | .error error => throw (IO.userError s!"raw multi-root checking failed: {reprStr error}")
  assertTrue (rawCompiled.keys == compiled.keys) "raw checking changed canonical roots"

  let artifact ← compiled.open
  assertTrue (artifact.keys == compiled.keys) "opening the cached recipe changed entry order"
  let session ← boot artifact
  let made ← execute session maker.key [word 10]
  let handle ← match made.value with
    | .function handle => pure handle
    | _ => throw (IO.userError "maker did not export an owned function")
  let first ← execute made.session consumer.key [.function handle, word 2]
  assertTrue (first.value == word 13) "another root lost the original globals or captured value"
  let second ← execute first.session duplicate.key [.function handle, word 3]
  assertTrue (second.value == word 14 && second.session.heapSize > first.session.heapSize)
    "duplicate root execution did not restart from the captured value across world extension"
  let mirrored ← execute second.session mirror.key [.function handle]
  assertTrue (mirrored.value == .function handle) "another root re-exported a different function capability"
  let boxed ← execute mirrored.session box.key [.function handle]
  let unboxed ← execute boxed.session unbox.key [boxed.value]
  assertTrue (unboxed.value == .function handle) "nominal multi-root exchange changed the function identity"
  let keptWord ← execute unboxed.session keepWord.key [word 41]
  let keptBool ← execute keptWord.session keepBool.key [.bool true]
  assertTrue (keptWord.value == word 41 && keptBool.value == .bool true)
    "ground generic roots did not run in the shared catalog"
  let checkpoint ← match keptBool.session.start consumer.key [.function handle, word 4] with
    | .ok checkpoint => pure checkpoint
    | .error error => throw (IO.userError s!"multi-root checkpoint rejected: {reprStr error}")
  let next ← match ← checkpoint.resume 2 with
    | .outOfFuel next => pure next
    | _ => throw (IO.userError "multi-root checkpoint failed to suspend")
  match ← next.resume 65536 with
  | .succeeded completion => assertTrue (completion.value == word 15) "multi-root resume changed the captured value"
  | _ => throw (IO.userError "multi-root checkpoint failed to finish")
  match session.authenticate 1024 functionType (.function handle) with
  | .error {code := .unknownHandle, ..} => pure ()
  | _ => throw (IO.userError "pre-export session snapshot lost unknown-handle rejection")
  let sibling ← boot artifact
  match sibling.authenticate 1024 functionType (.function handle) with
  | .error {code := .foreignSession, ..} => pure ()
  | _ => throw (IO.userError "another session lost foreign-session rejection")
  let reopened ← compiled.open
  let foreign ← boot reopened
  match foreign.authenticate 1024 functionType (.function handle) with
  | .error {code := .foreignArtifact, ..} => pure ()
  | _ => throw (IO.userError "another opened artifact lost foreign-artifact rejection")

  let missing := SourceCoreCompiler.Seed.named moduleId "missing"
  match compileChecked program [maker.seed, missing] options with
  | .error (.compilation (.seed 1 actual (.unknownName actualModule "missing"))) =>
      assertTrue (decide (actual = missing ∧ actualModule = moduleId)) "seed failure lost selector metadata"
  | _ => throw (IO.userError "seed failure lost its caller index")
  match compileChecked program [.named moduleId "keep"] options with
  | .error (.compilation (.seed 0 _ (.typeArgumentArityMismatch _ 1 0))) => pure ()
  | _ => throw (IO.userError "generic seed with wrong arity was accepted")
  match compileChecked program seeds { options with specializationBudget := 0 } with
  | .error (.compilation (.specializationBudgetExhausted _ _)) => pure ()
  | _ => throw (IO.userError "specialization exhaustion was hidden")
  let empty ← match compileChecked program [] options with
    | .ok empty => pure empty
    | .error error => throw (IO.userError s!"empty explicit root set failed: {reprStr error}")
  assertTrue (empty.rootCount == 0 && empty.keys.isEmpty) "empty root set gained an implicit main"
  let emptyArtifact ← empty.open
  let emptySession ← boot emptyArtifact
  match emptySession.start maker.key [word 10] with
  | .error {code := .missingEntry key, ..} => assertTrue (key == maker.key) "missing cached entry key changed"
  | _ => throw (IO.userError "empty artifact ran an uncompiled root")
  let invalid : Workspace.RawWorkspace := { workspace with
    mainSources := [{ path := "main.solc", content := "function broken() returns (Word) { return absent; }" }] }
  match compile invalid [] options with
  | .error (.compilation (.checking _)) => pure ()
  | _ => throw (IO.userError "raw facade bypassed source checking for an empty root list")
  IO.println "cached multi-root source compiler and shared owned handles GREEN"

end Tests.SourceCompilerSession
end

section
-- leanmerge: from Solcore.Test.SourceCompilerSourceBoundaryObservations
/-! Concrete observations of the existing public source-value boundary.
These checked fixtures use the exact cached artifact also prepared for the
common public session. Internal observations pin raw prefix compatibility. The initial prefix is validated and inert;
public captured-closure arguments remain rejected. -/

set_option autoImplicit false

namespace Tests.SourceCompilerSourceBoundaryObservations

open Solcore Solcore.Frontend SourceInference

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "enum Box<T> { Box(T) }",
    "function proxyEcho(value: @Word) returns (@Word) { return value; }",
    "function proxyLookup(table: mapping(@Word => Word)) returns (Word) { return table[@Word]; }",
    "function proxyMissing(table: mapping(Word => @Word)) returns (@Word) { return table[9]; }",
    "function mappingEcho(value: mapping(Word => Word)) returns (mapping(Word => Word)) { return value; }",
    "function boxEcho(value: Box<Word>) returns (Box<Word>) { return value; }",
    "function boxMatch(value: Box<Word>) returns (Word) { match (value) { case .Box(inner) { return inner; } default { return 99; } } }",
    "function scalar(value: Word) returns (Word) { return value; }",
    "function returnClosure() returns (function() returns (Word)) { let captured: Word = 7; return lam() -> Word { return captured; }; }",
    "function unusedPoly(captured: Word) returns (Word) { let f = lam(value) { return (value, captured); }; return captured; }",
    "function apply(f: function(Word) returns (Word), value: Word) returns (Word) { let retained: function(Word) returns (Word) = scalar; return f(value); }",
    "function applyUnselected(f: function(Word) returns (Word), value: Word) returns (Word) { return f(value); }",
    "function invokeUnit(f: function() returns (Word)) returns (Word) { return f(); }",
    "function applyInteger(f: function(Word) returns (integer), value: Word) returns (integer) { return f(value); }"
  ] }] }

private def compile (program : CheckedProgram) (name : String) : IO SourceCompilerFeatureSupport.Entry :=
  SourceCompilerFeatureSupport.compileNamed program name []
    {specializationBudget := 128, compilationFuel := 1000}

private def options : SourceCoreExecution.RunOptions := { inputValidationFuel := 128, executionFuel := 10000 }

private def completed (compiled : SourceCompilerFeatureSupport.Entry) (arguments : List SourceTypedRuntime.Value)
    (state : SourceTypedRuntime.RuntimeState := {}) : IO (SourceTypedRuntime.Value × SourceTypedRuntime.RuntimeState) := do
  let result ← SourceCompilerFeatureSupport.get "retained boundary execution"
    (compiled.cached.run compiled.key arguments options.inputValidationFuel options.executionFuel state)
  match result.observation with
  | .done value state => pure (value, state)
  | other => throw (IO.userError s!"source boundary execution failed: {reprStr other}")

private def wordResult (compiled : SourceCompilerFeatureSupport.Entry) (arguments : List SourceTypedRuntime.Value) (expected : Nat)
    (state : SourceTypedRuntime.RuntimeState := {}) : IO SourceTypedRuntime.RuntimeState := do
  let (value, state) ← completed compiled arguments state
  match value with
  | .word actual => assertTrue (actual == word expected) "source boundary Word result changed"; pure state
  | _ => throw (IO.userError "source boundary result was not Word")

example (type : TypeSystem.Ty) :
    SourceTypedRuntime.runtimeType (SourceCoreRawMetadata.runtimeType type) = SourceTypedRuntime.runtimeType type := by
  exact SourceCoreRawMetadata.runtimeType_sourceValues type

/- The metadata view keeps a fixed-width integer type, so word operations never
apply to it; the source runtime gives it the runtime type `word`. -/
example (type : TypeSystem.FixedInteger) :
    SourceCoreRawMetadata.runtimeType (.fixed type) = .fixed type ∧
      SourceTypedRuntime.runtimeType (.fixed type) = .word := ⟨rfl, rfl⟩

example (signatures : ProgramSignatures) (instantiation : DataConstructorInstantiation) :
    SourceCoreRawMetadata.constructorAuthentic signatures instantiation =
      SourceTypedRuntime.validConstructorInstantiation signatures instantiation := rfl

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"source boundary checking failed: {reprStr error}")
  let proxy ← compile program "proxyEcho"
  match (← completed proxy [.proxy (.comptime .word)]).1 with
  | .proxy (.comptime .word) => pure ()
  | _ => throw (IO.userError "accepted proxy metadata was erased")
  let lookup ← compile program "proxyLookup"
  let rawProxyMap : SourceTypedRuntime.Value := .mapping (.proxy .word) .word
    [(.proxy (.comptime .word), .word (word 7))]
  discard <| wordResult lookup [rawProxyMap] 0
  discard <| wordResult lookup [.mapping (.proxy .word) .word [(.proxy .word, .word (word 7))]] 7
  let missing ← compile program "proxyMissing"
  match (← completed missing [.mapping .word (.proxy (.comptime .word)) []]).1 with
  | .proxy (.comptime .word) => pure ()
  | _ => throw (IO.userError "mapping default ignored the actual raw value header")
  let mapping ← compile program "mappingEcho"
  let rawMap : SourceTypedRuntime.Value := .mapping (.comptime .word) (.comptime .word)
    [(.word (word 3), .word (word 7)), (.word (word 3), .word (word 9))]
  assertTrue (reprStr (← completed mapping [rawMap]).1 == reprStr rawMap)
    "mapping raw header or duplicate entry order changed"
  let box ← match program.signatures.dataTypes.filter (·.name == "Box") with
    | [signature] => pure signature
    | _ => throw (IO.userError "source boundary Box signature missing")
  let (parameter, constructor) ← match box.parameters, box.constructors with
    | [parameter], [constructor] => pure (parameter, constructor)
    | _, _ => throw (IO.userError "source boundary Box signature malformed")
  let stagedMetadata : DataConstructorInstantiation := {
    constructor := constructor.id, parameterSubstitution := [(parameter, .comptime .word)]
    payloadTypes := [.comptime .word], resultType := .nominal box.id [.comptime .word] }
  let ordinaryMetadata : DataConstructorInstantiation := {
    constructor := constructor.id, parameterSubstitution := [(parameter, .word)]
    payloadTypes := [.word], resultType := .nominal box.id [.word] }
  let echo ← compile program "boxEcho"
  match (← completed echo [.constructed stagedMetadata [.word (word 7)]]).1 with
  | .constructed actual _ => assertTrue (actual == stagedMetadata) "authenticated nominal metadata changed"
  | _ => throw (IO.userError "source boundary nominal result changed shape")
  let matchBox ← compile program "boxMatch"
  let noMatch ← wordResult matchBox [.constructed stagedMetadata [.word (word 7)]] 99
  let matched ← wordResult matchBox [.constructed ordinaryMetadata [.word (word 7)]] 7
  assertTrue (noMatch.heap.length == 2 && matched.heap.length == 3)
    "hidden scrutinee or successful pattern binder source allocation changed"
  let factory ← compile program "returnClosure"
  let (closure, initial) ← completed factory []
  let withClosure : SourceTypedRuntime.RuntimeState := {
    heap := initial.heap ++ [{type := .function .unit .word, value := some closure}] }
  let (_, reused) ← completed factory [] withClosure
  /- Each run allocates `captured` and the returned closure's snapshot copy of
  it, after the given prefix. -/
  assertTrue (reprStr (reused.heap.take withClosure.heap.length) == reprStr withClosure.heap && reused.heap.length == 5)
    "accepted existing closure heap prefix changed"
  /- Old code validation checks capture readability, not lexical type alignment.
  This prefix cannot be reached by any accepted public function input. -/
  let readablePrefix : SourceTypedRuntime.RuntimeState := { heap := [
    {type := .bool, value := some (.bool true)},
    {type := .function .unit .word, value := some closure}] }
  let (_, reusedReadable) ← completed factory [] readablePrefix
  assertTrue (reprStr (reusedReadable.heap.take 2) == reprStr readablePrefix.heap)
    "accepted inert readable closure prefix changed"
  let scalar ← compile program "scalar"
  let openPrefix : SourceTypedRuntime.RuntimeState := { heap := [
    {type := .error, value := none}, {type := .word, value := some (.word (word 99))}] }
  let scalarState ← wordResult scalar [.word (word 8)] 8 openPrefix
  assertTrue (reprStr (scalarState.heap.take 2) == reprStr openPrefix.heap && scalarState.heap.length == 3)
    "uninitialized open source prefix was rejected or changed"
  let unused ← compile program "unusedPoly"
  let unusedState ← wordResult unused [.word (word 8)] 8
  /- The generalized `let` copies `captured` before its principal, which
  captures the copy. -/
  match unusedState.heap with
  | [_, _, {type := .function _ _, value := some (.closure _ _ _ _ _ captures _)}] =>
      assertTrue (captures.map (fun capture => capture.2.index) == [1])
        "unused principal closure did not capture its snapshot copy"
  | _ => throw (IO.userError "unused generalized source binding did not retain its principal closure heap cell")
  let key : SourceSpecialization.SpecializationKey ← match program.signatures.functions.filter (·.name == "scalar") with
    | [signature] => pure ⟨signature.id, []⟩
    | _ => throw (IO.userError "source boundary selected global key missing")
  let apply ← compile program "apply"
  let globalState ← wordResult apply [.global key [], .word (word 8)] 8
  assertTrue (globalState.heap.length == 4) "global input/callee parameter allocation changed"
  let unselected ← compile program "applyUnselected"
  let rejectedGlobal ← SourceCompilerFeatureSupport.get "unselected global audit"
    (unselected.cached.run unselected.key [.global key [], .word (word 8)] options.inputValidationFuel options.executionFuel)
  match rejectedGlobal.observation with
  | .fault (.typeMismatch _ _) _ => pure ()
  | _ => throw (IO.userError "a global outside the selected plan was accepted")
  let invoke ← compile program "invokeUnit"
  let rejectedClosure ← SourceCompilerFeatureSupport.get "raw closure audit"
    (invoke.cached.run invoke.key [closure] options.inputValidationFuel options.executionFuel)
  match rejectedClosure.observation with
  | .fault (.typeMismatch _ _) _ => pure ()
  | _ => throw (IO.userError "public raw captured closure argument was accepted")
  let builtin ← compile program "applyInteger"
  match (← completed builtin [.builtin .wordToInteger, .word (word 8)]).1 with
  | .integer 8 => pure ()
  | _ => throw (IO.userError "public builtin function input changed")
  let malformedPrefix : SourceTypedRuntime.RuntimeState := {
    heap := [{type := .word, value := some (.bool true)}] }
  let malformedInput ← SourceCompilerFeatureSupport.get "input ordering audit"
    (scalar.cached.run scalar.key [.bool true] options.inputValidationFuel options.executionFuel malformedPrefix)
  match malformedInput.observation with
  | .fault (.typeMismatch .word (some .bool)) _ => pure ()
  | _ => throw (IO.userError "public input failure did not precede initial heap rejection")
  -- The public data carrier keeps the same accepted metadata and order.
  unless (← proxy.run [.proxy (.comptime .word)]) == .proxy (.comptime .word) do
    throw (IO.userError "public proxy metadata changed")
  unless (← lookup.run [.mapping (.proxy .word) .word
      [(.proxy (.comptime .word), .word (word 7))]]) == .word (word 0) do
    throw (IO.userError "public proxy-key comparison erased raw metadata")
  unless (← missing.run [.mapping .word (.proxy (.comptime .word)) []]) == .proxy (.comptime .word) do
    throw (IO.userError "public mapping default lost its raw value header")
  let publicMap : SourceCoreExecution.Value := .mapping (.comptime .word) (.comptime .word)
    [(.word (word 3), .word (word 7)), (.word (word 3), .word (word 9))]
  unless (← mapping.run [publicMap]) == publicMap do
    throw (IO.userError "public mapping metadata or duplicate order changed")
  let publicBox : SourceCoreExecution.Value := .constructed stagedMetadata [.word (word 7)]
  unless (← echo.run [publicBox]) == publicBox && (← matchBox.run [publicBox]) == .word (word 99) do
    throw (IO.userError "public nominal metadata or matching changed")
  IO.println "public raw metadata, function inputs and inert source heap observations GREEN"

end Tests.SourceCompilerSourceBoundaryObservations
end

section
-- leanmerge: from Solcore.Test.SourceCompilerUnifiedRouting
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.runTrusted
#check_failure Solcore.Frontend.SourceTypedRuntime.runDeepCertifiedWithValidationFuel
#check_failure Solcore.Frontend.SourceCoreExecution.Checkpoint.mk

/-! Public sessions execute one cached Core artifact. Internal compatibility
observations retain raw metadata, errors and the inert source heap prefix;
public checkpoints resume native execution without a backend selector. -/
set_option autoImplicit false
namespace Tests.SourceCompilerUnifiedRouting
open Solcore Solcore.Frontend SourceInference

private def w (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "function scalar(value: Word) returns (Word) { return value; }",
    "function mappingEcho(value: mapping(Word => Word)) returns (mapping(Word => Word)) { return value; }",
    "function apply(f: function(Word) returns (Word), value: Word) returns (Word) { let retained: function(Word) returns (Word) = scalar; return f(value); }",
    "function integerApply(f: function(Word) returns (integer), value: Word) returns (integer) { return f(value); }",
    "function capture(start: Word) returns (Word) { let value = start; let f = lam(step: Word) { value += step; return value; }; f(3); return f(4); }",
    "function failAfterWrite() returns (Word) { let value: Word = 1; let fail = lam() -> Word { value += 2; let missing: Word; return missing; }; return fail(); }",
    "function spin() returns (Word) { return spin(); }"
  ] }] }

private def compile (program : CheckedProgram) (name : String) : IO SourceCompilerFeatureSupport.Entry :=
  SourceCompilerFeatureSupport.compileNamed program name []
    {specializationBudget := 256, compilationFuel := 1000}

private def initial : SourceTypedRuntime.RuntimeState := { heap := [⟨.error, none⟩, ⟨.word, some (.word (w 99))⟩] }
private def options : SourceCoreExecution.RunOptions := { inputValidationFuel := 500, executionFuel := 150000 }
private def completed (compiled : SourceCompilerFeatureSupport.Entry) (arguments : List SourceTypedRuntime.Value) :
    IO (SourceTypedRuntime.Value × SourceTypedRuntime.RuntimeState) := do
  let result ← get "cached source observation" (compiled.cached.run compiled.key arguments
    options.inputValidationFuel options.executionFuel initial)
  match result.observation with
  | .done value final =>
      assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap) "inert prefix changed"
      pure (value, final)
  | other => throw (IO.userError s!"cached source observation did not complete: {reprStr other}")

example {compiled : SourceCoreUnifiedCompilation.Compiled} (result : SourceCoreUnifiedCompilation.Result compiled)
    {value : SourceTypedRuntime.Value} {final : SourceTypedRuntime.RuntimeState}
    (done : result.observation = .done value final) :
    ∃ execution, result.execution = some execution ∧
      SourceTypedRuntime.PreparedDeepExecution compiled.indexed.base.sourceProgram compiled.indexed.base.validationPlan
        execution.root.argumentTypes execution.root.expected execution.arguments execution.initial value final :=
  result.done_certificate done

def run : IO Unit := do
  let program ← get "routing checking" (checkProgram workspace)
  let mapping ← compile program "mappingEcho"
  let raw : SourceTypedRuntime.Value := .mapping (.comptime .word) (.comptime .word)
    [(.word (w 1), .word (w 7)), (.word (w 1), .word (w 9))]
  assertTrue (reprStr (← completed mapping [raw]).1 == reprStr raw) "raw header or ordered duplicate mapping changed"
  let scalar ← match program.signatures.functions.filter (·.name == "scalar") with
    | [signature] => pure (⟨signature.id, []⟩ : SourceSpecialization.SpecializationKey)
    | _ => throw (IO.userError "routing scalar missing")
  let apply ← compile program "apply"
  assertTrue (reprStr (← completed apply [.global scalar [], .word (w 8)]).1 == reprStr (.word (w 8) : SourceTypedRuntime.Value))
    "authenticated global argument changed"
  let builtin ← compile program "integerApply"
  assertTrue (reprStr (← completed builtin [.builtin .wordToInteger, .word (w 8)]).1 == reprStr (.integer 8 : SourceTypedRuntime.Value))
    "builtin argument changed"
  let capture ← compile program "capture"
  let paused ← get "native source checkpoint" (capture.cached.run capture.key [.word (w 10)] options.inputValidationFuel 0 initial)
  match paused.observation with
  | .outOfFuel state => assertTrue (reprStr state == reprStr initial) "zero fuel changed source prefix"
  | other => throw (IO.userError s!"zero fuel did not suspend: {reprStr other}")
  let resumed ← get "native source resume" (paused.resume 150000)
  /- Closures capture by value: each call of `f` starts again from the
  captured `value`, so `f(4)` returns 14. -/
  match resumed.observation with
  | .done (.word value) final =>
      assertTrue (value == w 14 && reprStr (final.heap.take 2) == reprStr initial.heap) "resumed captures or source prefix changed"
  | other => throw (IO.userError s!"resumed source checkpoint did not complete: {reprStr other}")
  let failure ← compile program "failAfterWrite"
  let failed ← get "cached source language fault" (failure.cached.run failure.key [] options.inputValidationFuel options.executionFuel initial)
  match failed.observation with
  | .fault (.uninitializedLocal _) state =>
      assertTrue (state.heap.any fun cell => match cell.value with | some (.word value) => value == w 3 | _ => false)
        "language failure lost the closure call's preceding write to its copy"
  | other => throw (IO.userError s!"public source fault changed: {reprStr other}")
  let spin ← compile program "spin"
  let paused ← get "recursive native checkpoint" (spin.cached.run spin.key [] options.inputValidationFuel 43 initial)
  let continued ← get "recursive native resume" (paused.resume 211)
  match continued.observation with
  | .outOfFuel _ => pure ()
  | other => throw (IO.userError s!"recursive native resume unexpectedly terminated: {reprStr other}")
  let artifact ← apply.execution.open
  let session ← SourceCompilerFeatureSupport.boot artifact
  let named ← get "public selected global" (← session.named scalar)
  match ← named.session.run apply.key [named.value, .word (w 8)] {executionFuel := 300000} with
  | .ok (.succeeded result) => assertTrue (result.value == .word (w 8)) "public selected global changed"
  | _ => throw (IO.userError "public selected global invocation failed")
  let rawPublic : SourceCoreExecution.Value := .mapping (.comptime .word) (.comptime .word)
    [(.word (w 1), .word (w 7)), (.word (w 1), .word (w 9))]
  assertTrue ((← mapping.run [rawPublic]) == rawPublic) "public mapping header/order changed"
  capture.checkResume [.word (w 10)] (.word (w 14)) 0
  let publicFailure ← failure.invoke []
  match publicFailure.outcome with
  | .failed reason _ =>
      match ← publicFailure.diagnostic reason with
      | some {error := .uninitializedLocal _, ..} => pure ()
      | _ => throw (IO.userError "public fault classification changed")
  | _ => throw (IO.userError "public fault failed to occur")
  let publicSpin ← spin.invoke [] {executionFuel := 43}
  match publicSpin.outcome with
  | .outOfFuel checkpoint =>
      match ← checkpoint.resume 211 with
      | .outOfFuel _ => pure ()
      | _ => throw (IO.userError "public recursive resume unexpectedly terminated")
  | _ => throw (IO.userError "public recursive invocation unexpectedly terminated")
  IO.println "common public sessions and retained prefix audits use cached Core with typed resume GREEN"

end Tests.SourceCompilerUnifiedRouting
end

section
-- leanmerge: from Solcore.Test.SourceConstructorVisibility
/-!
Focused end-to-end checks for constructor visibility at the source-inference
boundary.  These phase-eight regressions run from the aggregate test suite.
-/

set_option autoImplicit false

namespace Tests.SourceConstructorVisibility

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def workspace (entry : String)
    (sources : List (String × String)) : Workspace.RawWorkspace := {
  entry
  mainSources := sources.map fun source => {
    path := source.1
    content := source.2
  }
  externalLibraries := []
}

private def workspaceWithExternal (entry : String)
    (sources : List (String × String)) (externalName : String)
    (externalSources : List (String × String)) : Workspace.RawWorkspace := {
  entry
  mainSources := sources.map fun source => {
    path := source.1
    content := source.2
  }
  externalLibraries := [{
    name := externalName
    sources := externalSources.map fun source => {
      path := source.1
      content := source.2
    }
  }]
}

private def expectAccepted (label entry : String)
    (sources : List (String × String)) : IO Unit := do
  match loadAndCheckProgram (workspace entry sources) with
  | .ok _ => pure ()
  | .error errors => throw (IO.userError
      s!"{label} was rejected: {reprStr errors}")

private def expectUnknownConstructor (label entry : String)
    (sources : List (String × String)) (qualifiers : List String)
    (name : String) : IO Unit := do
  match loadAndCheckProgram (workspace entry sources) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body failure =>
            failure.error == .unknownConstructor qualifiers name
        | _ => false)
        s!"{label} reported the wrong failure: {reprStr errors}"
  | .ok _ => throw (IO.userError
      s!"{label} exposed a hidden constructor")

private def expectBodyError (label : String)
    (workspace : Workspace.RawWorkspace) (accept : Error → Bool) : IO Unit := do
  match loadAndCheckProgram workspace with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body failure => accept failure.error
        | _ => false)
        s!"{label} reported the wrong failure: {reprStr errors}"
  | .ok _ => throw (IO.userError s!"{label} was unexpectedly accepted")

private def testLocalAndImportedVisibility : IO Unit := do
  expectAccepted "local defining module" "local.solc" [
    ("local.solc", String.intercalate "\n" [
      "enum Box { Wrap(Word) }",
      "export {Box};",
      "function local(value: Word) returns (Box) { return Box.Wrap(value); }"
    ])
  ]
  let opaqueProvider := String.intercalate "\n" [
    "enum Box { Empty, Wrap(Word) }",
    "export {Box};"
  ]
  let opaqueConsumer := String.intercalate "\n" [
    "import provider;",
    "function bad(value: Word) returns (provider.Box) {",
    "  return provider.Box.Wrap(value);",
    "}"
  ]
  expectUnknownConstructor "opaque named export" "consumer.solc"
    [("provider.solc", opaqueProvider), ("consumer.solc", opaqueConsumer)]
    ["provider", "Box"] "Wrap"
  let visibleProvider := String.intercalate "\n" [
    "enum Box { Empty, Wrap(Word) }",
    "export {Box(Wrap)};"
  ]
  let visibleConsumer := String.intercalate "\n" [
    "import provider;",
    "function good(value: Word) returns (provider.Box) {",
    "  return provider.Box.Wrap(value);",
    "}"
  ]
  expectAccepted "selected imported constructor" "consumer.solc"
    [("provider.solc", visibleProvider), ("consumer.solc", visibleConsumer)]
  let selectedConsumer := String.intercalate "\n" [
    "import {Box} from provider;",
    "function good(value: Word) returns (Box) { return Box.Wrap(value); }"
  ]
  expectAccepted "unqualified selected type import" "selected.solc"
    [("provider.solc", visibleProvider), ("selected.solc", selectedConsumer)]
  expectUnknownConstructor "opaque unqualified selected type import"
    "selected.solc"
    [("provider.solc", opaqueProvider), ("selected.solc", selectedConsumer)]
    ["Box"] "Wrap"

private def testSubsetAndContextualVisibility : IO Unit := do
  let provider := String.intercalate "\n" [
    "enum Choice { Shown(Word), Hidden(Word) }",
    "export {Choice(Shown)};"
  ]
  let hidden := String.intercalate "\n" [
    "import provider;",
    "function bad(value: Word) returns (provider.Choice) {",
    "  return provider.Choice.Hidden(value);",
    "}"
  ]
  expectUnknownConstructor "unselected explicit constructor" "hidden.solc"
    [("provider.solc", provider), ("hidden.solc", hidden)]
    ["provider", "Choice"] "Hidden"
  let contextual := String.intercalate "\n" [
    "import provider;",
    "function bad(value: Word) returns (provider.Choice) {",
    "  return .Hidden(value);",
    "}"
  ]
  expectUnknownConstructor "unselected contextual constructor" "contextual.solc"
    [("provider.solc", provider), ("contextual.solc", contextual)] [] "Hidden"

private def testReExportVisibility : IO Unit := do
  let provider := String.intercalate "\n" [
    "enum Box { Wrap(Word) }",
    "export {Box(*)};"
  ]
  let consumer := String.intercalate "\n" [
    "import facade;",
    "function use(value: Word) returns (facade.Box) {",
    "  return facade.Box.Wrap(value);",
    "}"
  ]
  expectAccepted "wildcard re-export" "consumer.solc" [
    ("provider.solc", provider),
    ("facade.solc", "export provider.*;"),
    ("consumer.solc", consumer)
  ]
  expectUnknownConstructor "named re-export" "consumer.solc" [
    ("provider.solc", provider),
    ("facade.solc", "export provider.{Box};"),
    ("consumer.solc", consumer)
  ] ["facade", "Box"] "Wrap"

private def testAliasConstructorBoundary : IO Unit := do
  expectAccepted "contextual constructor through transparent alias" "main.solc" [
    ("main.solc", String.intercalate "\n" [
      "enum Box<T> { Wrap(T) }",
      "type WordBox = Box<Word>;",
      "function good(value: Word) returns (WordBox) { return .Wrap(value); }"
    ])
  ]
  let qualifiedAlias := workspace "main.solc" [
    ("main.solc", String.intercalate "\n" [
      "enum Box<T> { Wrap(T) }",
      "type WordBox = Box<Word>;",
      "function bad(value: Word) returns (WordBox) {",
      "  return WordBox.Wrap(value);",
      "}"
    ])
  ]
  expectBodyError "type alias constructor namespace" qualifiedAlias fun error =>
    match error with
    | .unsupportedExpression kind => kind == "field"
    | _ => false

  let provider := String.intercalate "\n" [
    "enum Box<T> { Wrap(T), Hidden(T) }",
    "type WordBox = Box<Word>;",
    "export {Box(Wrap), WordBox};"
  ]
  let imported := String.intercalate "\n" [
    "import {Box, WordBox} from provider;",
    "function good(value: Word) returns (WordBox) { return .Wrap(value); }"
  ]
  expectAccepted "imported contextual constructor through transparent alias"
    "imported.solc" [("provider.solc", provider), ("imported.solc", imported)]
  let hidden := String.intercalate "\n" [
    "import {Box, WordBox} from provider;",
    "function bad(value: Word) returns (WordBox) { return .Hidden(value); }"
  ]
  expectUnknownConstructor "hidden constructor through imported alias"
    "hidden.solc" [("provider.solc", provider), ("hidden.solc", hidden)]
    [] "Hidden"
  let aliasOnly := String.intercalate "\n" [
    "import {WordBox} from provider;",
    "function bad(value: Word) returns (WordBox) { return .Wrap(value); }"
  ]
  expectUnknownConstructor "alias import without constructor visibility"
    "alias_only.solc"
    [("provider.solc", provider), ("alias_only.solc", aliasOnly)] [] "Wrap"

private def testCanonicalPathDoesNotBypassImports : IO Unit := do
  let provider :=
    "enum Box { Wrap(Word) } export {Box(*)};"
  let consumer := String.intercalate "\n" [
    "function bad(value: Word) returns (Word) {",
    "  return provider.Box.Wrap(value);",
    "}"
  ]
  expectBodyError "unimported canonical constructor path"
    (workspace "consumer.solc" [
      ("provider.solc", provider), ("consumer.solc", consumer)
    ]) fun error =>
      error == .unsupportedExpression "field"

private def testLibraryIdentityIsolation : IO Unit := do
  let mainProvider :=
    "enum Box { MainOnly } export {Box(MainOnly)};"
  let externalProvider :=
    "enum Box { ExternalOnly } export {Box(ExternalOnly)};"
  let accepted := String.intercalate "\n" [
    "import * as Main from shared;",
    "import * as Ext from @dep.shared;",
    "function mainBox() returns (Main.Box) { return Main.Box.MainOnly; }",
    "function externalBox() returns (Ext.Box) { return Ext.Box.ExternalOnly; }"
  ]
  let acceptedWorkspace := workspaceWithExternal "accepted.solc"
    [("shared.solc", mainProvider), ("accepted.solc", accepted)] "dep"
    [("shared.solc", externalProvider)]
  match loadAndCheckProgram acceptedWorkspace with
  | .ok _ => pure ()
  | .error errors => throw (IO.userError
      s!"same-path library-local constructors were rejected: {reprStr errors}")
  let leaked := String.intercalate "\n" [
    "import * as Main from shared;",
    "import * as Ext from @dep.shared;",
    "function bad() returns (Main.Box) { return Main.Box.ExternalOnly; }"
  ]
  let leakedWorkspace := workspaceWithExternal "leaked.solc"
    [("shared.solc", mainProvider), ("leaked.solc", leaked)] "dep"
    [("shared.solc", externalProvider)]
  expectBodyError "main/external constructor visibility isolation"
    leakedWorkspace fun error =>
      error == .unknownConstructor ["Main", "Box"] "ExternalOnly"
  let reverseLeak := String.intercalate "\n" [
    "import * as Main from shared;",
    "import * as Ext from @dep.shared;",
    "function bad() returns (Ext.Box) { return Ext.Box.MainOnly; }"
  ]
  let reverseLeakWorkspace := workspaceWithExternal "reverse.solc"
    [("shared.solc", mainProvider), ("reverse.solc", reverseLeak)] "dep"
    [("shared.solc", externalProvider)]
  expectBodyError "external/main constructor visibility isolation"
    reverseLeakWorkspace fun error =>
      error == .unknownConstructor ["Ext", "Box"] "MainOnly"

def testSourceConstructorVisibility : IO Unit := do
  testLocalAndImportedVisibility
  testSubsetAndContextualVisibility
  testReExportVisibility
  testAliasConstructorBoundary
  testCanonicalPathDoesNotBypassImports
  testLibraryIdentityIsolation

end Tests.SourceConstructorVisibility

namespace Tests

/-- Run the source-level constructor-visibility regressions. -/
def testSourceConstructorVisibility : IO Unit :=
  SourceConstructorVisibility.testSourceConstructorVisibility

end Tests
end

section
-- leanmerge: from Solcore.Test.SourceProgramExecution
/-! End-to-end regressions for the explicit public source execution pipeline. -/

set_option autoImplicit false

namespace Tests.SourceProgramExecution

open Solcore Solcore.Frontend Solcore.Frontend.SourceProgramExecution
open Solcore.TypeSystem

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def word (value : Nat) : Core.Word :=
  ⟨value % Core.wordModulus, Nat.mod_lt _ (by simp [Core.wordModulus])⟩

private def mainModule (path : String) : IO Workspace.ModuleId := do
  match Workspace.CanonicalSourcePath.parse path with
  | none => throw (IO.userError s!"invalid test module path `{path}`")
  | some canonical => pure {
      library := .main
      path := canonical.modulePath
    }

private def rawWorkspace (entry : String)
    (sources : List (String × String)) : Workspace.RawWorkspace := {
  entry
  mainSources := sources.map fun source => {
    path := source.1
    content := source.2
  }
  externalLibraries := []
}

private def basicSource : String := String.intercalate "\n" [
  "function identity<T>(value: T) returns (T) { return value; }",
  "function entry(value: Word, flag: Bool) returns (Word) {",
  "  return flag ? identity(value) : 7;",
  "}"
]

private def basicWorkspace : Workspace.RawWorkspace :=
  rawWorkspace "main.solc" [("main.solc", basicSource)]

private def generousLimits : Limits := {
  checkingFuel := 1024
  specializationBudget := 8
  executionFuel := 4096
}

private def testNamedSeedAndPreparedRun : IO Unit := do
  let moduleId ← mainModule "main.solc"
  let seed := Seed.named moduleId "entry"
  let prepared ← match prepare basicWorkspace seed generousLimits with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"named root preparation failed: {reprStr error}")
  assertTrue (decide (prepared.key.declaration.moduleId = moduleId ∧
      prepared.key.declaration.declarationIndex = 1 ∧
      prepared.key.arguments = [] ∧
      prepared.inputTypes = [.word, .bool]))
    "named root did not retain its explicit module, declaration, or inputs"
  let fortyOne : Core.Value := .word (word 41)
  assertTrue (decide (prepared.run? [fortyOne, .bool true] 4096 =
      some (.done fortyOne [])))
    "prepared named root did not execute its reachable generic call"
  assertTrue (decide (prepared.run? [fortyOne, .bool false] 4096 =
      some (.done (.word (word 7)) [])))
    "prepared named root did not execute its other conditional branch"
  assertTrue ((prepared.run? [.bool true, fortyOne] 4096).isNone)
    "prepared run? accepted runtime values in the wrong type order"

private def testDeclarationSeedAndStore : IO Unit := do
  let moduleId ← mainModule "main.solc"
  let declaration : Resolved.DeclarationId := {
    moduleId
    declarationIndex := 0
  }
  let seed := Seed.declaration declaration [.word]
  let input : Core.Value := .word (word 19)
  let store : Core.Store := [.bool false, .word (word 3)]
  match run basicWorkspace seed [input] generousLimits store with
  | .ok result =>
      assertTrue (decide (result = .done input store))
        "declaration root lost its generic argument, input, or supplied store"
  | .error error => throw (IO.userError
      s!"declaration root execution failed: {reprStr error}")

private def testModuleQualifiedName : IO Unit := do
  let mainId ← mainModule "main.solc"
  let otherId ← mainModule "other.solc"
  let workspace := rawWorkspace "main.solc" [
    ("main.solc", "function entry() returns (Word) { return 11; }"),
    ("other.solc", "function entry() returns (Word) { return 22; }")
  ]
  match run workspace (Seed.named otherId "entry") [] generousLimits with
  | .ok result =>
      assertTrue (decide (result = .done (.word (word 22)) []))
        "module-qualified seed followed the raw workspace entry instead"
  | .error error => throw (IO.userError
      s!"module-qualified root failed: {reprStr error}")
  match run workspace (Seed.named mainId "entry") [] generousLimits with
  | .ok result =>
      assertTrue (decide (result = .done (.word (word 11)) []))
        "explicit main-module seed selected another module"
  | .error error => throw (IO.userError
      s!"main-module root failed: {reprStr error}")

private def testDeferredIntegerOperators : IO Unit := do
  let moduleId ← mainModule "main.solc"
  let workspace := rawWorkspace "main.solc" [("main.solc",
    String.intercalate "\n" [
      "function accept(value: Word) returns (Word) { return value; }",
      "function nestedAdd() returns (Word) { return accept(1 + 1); }",
      "function nestedNot() returns (Word) { return accept(~1); }"
    ])]
  match run workspace (Seed.named moduleId "nestedAdd") [] generousLimits with
  | .ok result =>
      assertTrue (decide (result = .done (.word (word 2)) []))
        "public execution changed deferred nested addition"
  | .error error => throw (IO.userError
      s!"public deferred addition failed: {reprStr error}")
  match run workspace (Seed.named moduleId "nestedNot") [] generousLimits with
  | .ok result =>
      assertTrue (decide (result = .done (.word (word 1).bitNot) []))
        "public execution changed deferred nested complement"
  | .error error => throw (IO.userError
      s!"public deferred complement failed: {reprStr error}")

private def testDefaultedIntegerLiterals : IO Unit := do
  let moduleId ← mainModule "main.solc"
  let workspace := rawWorkspace "main.solc" [("main.solc",
    "function defaulted() returns (Word) { let unused = 1; return 9; }")]
  match run workspace (Seed.named moduleId "defaulted") [] generousLimits with
  | .ok result =>
      assertTrue (decide (result = .done (.word (word 9)) []))
        "public execution did not default unconstrained integer literals to Word"
  | .error error => throw (IO.userError
      s!"public defaulted integer literal failed: {reprStr error}")

private def testDefaultImplementationPriority : IO Unit := do
  let moduleId ← mainModule "main.solc"
  let workspace := rawWorkspace "main.solc" [("main.solc",
    String.intercalate "\n" [
      "trait Add<T> {",
      "  function add(left: T, right: T) returns (T);",
      "}",
      "default impl<T> Add<T> {",
      "  function add(left: T, right: T) returns (T) { return left; }",
      "}",
      "impl Add<Word> {",
      "  function add(left: Word, right: Word) returns (Word) { return 73; }",
      "}",
      "function addWithEvidence<T>(left: T, right: T) returns (T) where T: Add {",
      "  return left + right;",
      "}",
      "function ordinary() returns (Word) { return addWithEvidence(1, 2); }",
      "function fallbackCase(left: Bool, right: Bool) returns (Bool) {",
      "  return addWithEvidence(left, right);",
      "}"
    ])]
  match run workspace (Seed.named moduleId "ordinary") [] generousLimits with
  | .ok result =>
      assertTrue (decide (result = .done (.word (word 73)) []))
        s!"an ordinary implementation did not outrank a matching default: {reprStr result}"
  | .error error => throw (IO.userError
      s!"public ordinary implementation execution failed: {reprStr error}")
  match run workspace (Seed.named moduleId "fallbackCase")
      [.bool false, .bool true] generousLimits with
  | .ok result =>
      assertTrue (decide (result = .done (.bool false) []))
        s!"a default implementation did not handle an unmatched ordinary tier: {reprStr result}"
  | .error error => throw (IO.userError
      s!"public default implementation execution failed: {reprStr error}")

private def testSeedErrors : IO Unit := do
  let moduleId ← mainModule "main.solc"
  let missingModule ← mainModule "missing.solc"
  match prepare basicWorkspace (Seed.named missingModule "entry") with
  | .error (.seed (.unknownModule actual)) =>
      assertTrue (decide (actual = missingModule))
        "unknown-module error changed its exact module"
  | result => throw (IO.userError
      s!"unknown seed module was accepted: {reprStr result}")
  match prepare basicWorkspace (Seed.named moduleId "absent") with
  | .error (.seed (.unknownName actual name)) =>
      assertTrue (decide (actual = moduleId ∧ name = "absent"))
        "unknown-name error changed its module or spelling"
  | result => throw (IO.userError
      s!"unknown root name was accepted: {reprStr result}")
  let identity : Resolved.DeclarationId := {
    moduleId
    declarationIndex := 0
  }
  match prepare basicWorkspace (Seed.declaration identity) with
  | .error (.seed (.typeArgumentArityMismatch actual expected supplied)) =>
      assertTrue (decide (actual = identity ∧ expected = 1 ∧ supplied = 0))
        "generic-arity error lost its declaration or counts"
  | result => throw (IO.userError
      s!"missing generic type argument was accepted: {reprStr result}")
  let openArgument : Ty := .variable ⟨77⟩
  match prepare basicWorkspace
      (Seed.declaration identity [openArgument]) generousLimits with
  | .error (.worklist (.specialization actual
        (.nonConcreteArgument _ (.flexible variableId)))) =>
      assertTrue (decide (actual = identity ∧ variableId = ⟨77⟩))
        "open generic argument lost its worklist-stage rejection"
  | result => throw (IO.userError
      s!"open generic type argument was accepted: {reprStr result}")
  let missing : Resolved.DeclarationId := {
    moduleId
    declarationIndex := 99
  }
  match prepare basicWorkspace (Seed.declaration missing) with
  | .error (.seed (.unknownDeclaration actual)) =>
      assertTrue (decide (actual = missing))
        "unknown-declaration error changed its identity"
  | result => throw (IO.userError
      s!"unknown declaration root was accepted: {reprStr result}")

private def testAmbiguousAndNonFunctionSeeds : IO Unit := do
  let moduleId ← mainModule "main.solc"
  let overloaded := rawWorkspace "main.solc" [("main.solc",
    String.intercalate "\n" [
      "function choose(value: Word) returns (Word) { return value; }",
      "function choose(value: Bool) returns (Bool) { return value; }"
    ])]
  match prepare overloaded (Seed.named moduleId "choose") with
  | .error (.seed (.ambiguousName actual name candidates)) =>
      assertTrue (decide (actual = moduleId ∧ name = "choose" ∧
          candidates.map (·.declarationIndex) = [0, 1]))
        "ambiguous name did not retain its ordered overload declarations"
  | result => throw (IO.userError
      s!"ambiguous root name was accepted: {reprStr result}")
  let traitWorkspace := rawWorkspace "main.solc" [("main.solc",
    String.intercalate "\n" [
      "trait Marker<T> {}",
      "function entry() returns (Word) { return 1; }"
    ])]
  let traitId : Resolved.DeclarationId := {
    moduleId
    declarationIndex := 0
  }
  match prepare traitWorkspace (Seed.declaration traitId [.word]) with
  | .error (.seed (.declarationNotFunction actual .trait)) =>
      assertTrue (decide (actual = traitId))
        "non-function seed error changed its declaration"
  | result => throw (IO.userError
      s!"trait declaration was accepted as an execution root: {reprStr result}")

private def testStageErrors : IO Unit := do
  let moduleId ← mainModule "main.solc"
  let malformed := rawWorkspace "main.solc" [("main.solc",
    "function broken(value: Missing) returns (Word) { return 1; }")]
  match prepare malformed (Seed.named moduleId "broken") with
  | .error (.checking (_ :: _)) => pure ()
  | result => throw (IO.userError
      s!"checking failure lost its pipeline stage: {reprStr result}")
  let noChecking : Limits := {
    checkingFuel := 0
    specializationBudget := 8
    executionFuel := 4096
  }
  match prepare basicWorkspace (Seed.named moduleId "entry") noChecking with
  | .error (.checking (_ :: _)) => pure ()
  | result => throw (IO.userError
      s!"checking fuel was not routed to source inference: {reprStr result}")
  let tight : Limits := {
    checkingFuel := 1024
    specializationBudget := 1
    executionFuel := 4096
  }
  match prepare basicWorkspace (Seed.named moduleId "entry") tight with
  | .error (.specializationBudgetExhausted next pendingCount) =>
      assertTrue (decide (next.declaration.moduleId = moduleId ∧
          next.declaration.declarationIndex = 0 ∧
          next.arguments = [.word] ∧ pendingCount = 1))
        "specialization frontier lost its exact next key or queue size"
  | result => throw (IO.userError
      s!"specialization exhaustion lost its public stage: {reprStr result}")
  let indirect := rawWorkspace "main.solc" [("main.solc",
    "function apply(f: function(Word) returns (Word), value: Word) returns (Word) { return f(value); }")]
  match prepare indirect (Seed.named moduleId "apply") generousLimits with
  | .error (.linking (.sourceCore {
      reason := .unsupportedType (.function .word .word), .. })) => pure ()
  | result => throw (IO.userError
      s!"indirect call did not retain its direct-linking rejection: {reprStr result}")
  let recursive := rawWorkspace "main.solc" [("main.solc",
    "function loop(value: Word) returns (Word) { return loop(value); }")]
  match prepare recursive (Seed.named moduleId "loop") generousLimits with
  | .error (.linking (.recursiveCallCycle key)) =>
      assertTrue (decide (key.declaration.moduleId = moduleId ∧
          key.declaration.declarationIndex = 0 ∧ key.arguments = []))
        "recursive direct-linking rejection lost its specialization key"
  | result => throw (IO.userError
      s!"recursive source root did not retain its direct-linking rejection: {reprStr result}")

private def testRuntimeBoundary : IO Unit := do
  let moduleId ← mainModule "main.solc"
  let seed := Seed.named moduleId "entry"
  match run basicWorkspace seed [.bool true, .bool false] generousLimits with
  | .error (.inputTypesMismatch expected actual) =>
      assertTrue (decide (expected = [.word, .bool] ∧
          actual = [.bool, .bool]))
        "runtime input mismatch lost its exact expected or actual types"
  | result => throw (IO.userError
      s!"ill-typed runtime inputs crossed the public pipeline: {reprStr result}")
  let noExecution : Limits := {
    generousLimits with executionFuel := 0
  }
  match run basicWorkspace seed [.word (word 41), .bool true] noExecution with
  | .ok (.outOfFuel _) => pure ()
  | result => throw (IO.userError
      s!"Core fuel exhaustion became a pipeline error: {reprStr result}")

/-- Exercise both explicit seed forms, all public stages, and runtime policy. -/
def testSourceProgramExecution : IO Unit := do
  testNamedSeedAndPreparedRun
  testDeclarationSeedAndStore
  testModuleQualifiedName
  testDeferredIntegerOperators
  testDefaultedIntegerLiterals
  testDefaultImplementationPriority
  testSeedErrors
  testAmbiguousAndNonFunctionSeeds
  testStageErrors
  testRuntimeBoundary
  IO.println "explicit raw-source check/specialize/link/run pipeline GREEN"

end Tests.SourceProgramExecution
end

section
-- leanmerge: from Solcore.Test.SourceRuntimeDeepValidationBoundary
/-! Core adapters can validate source heaps, captures and checked-code
provenance without acquiring a source execution entry point. Uninitialized
cells remain admissible, including opaque initial heap cells. -/

namespace Tests.SourceRuntimeDeepValidationBoundary
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open SourceTypedRuntime

#check Value.HasDeepTypeFuel
#check Value.HasPlanCode
#check RuntimeState.isDeeplySafe
#check RuntimeState.isDeeplySafe_sound
#check ClosureCodeAndEvidenceValid
#check InstantiatedLocalEvidenceValid
#check RuntimeSourceImage
#check PreparedDeepExecution

example (signatures : ProgramSignatures) (plan : SourceCompilationPlan.Plan) :
    ({ heap := [{ type := .error, value := none }] } : RuntimeState).isDeeplySafe
      0 signatures plan = true := by
  rfl

example (signatures : ProgramSignatures) (plan : SourceCompilationPlan.Plan) :
    ({ heap := [{ type := .error, value := none }] } : RuntimeState).HasDeepTypes
      signatures plan := by
  have accepted :
      ({ heap := [{ type := .error, value := none }] } : RuntimeState).isDeeplySafe
        0 signatures plan = true := rfl
  exact (RuntimeState.isDeeplySafe_sound accepted).hasDeepTypes

example (raw : TypeSystem.Ty) :
    defaultValue? 1 (.proxy raw) = some (.proxy raw) := rfl

example (rawKey rawValue : TypeSystem.Ty) :
    defaultValue? 1 (.mapping rawKey rawValue) =
      some (.mapping rawKey rawValue []) := rfl

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.runTrusted
#check_failure Solcore.Frontend.SourceTypedRuntime.runWithValidationFuel
#check_failure Solcore.Frontend.SourceTypedRuntime.invokeSpecialization
#check_failure Solcore.Frontend.SourceTypedRuntime.evaluate
#check_failure Solcore.Frontend.SourceTypedRuntime.executeStatement
#check_failure Solcore.Frontend.SourceTypedRuntime.runDeepCertifiedWithValidationFuel

end Tests.SourceRuntimeDeepValidationBoundary
end

section
-- leanmerge: from Solcore.Test.SourceRuntimeValidationBoundary
/-! Core adapters can preserve the existing source input contract and result
carrier without importing any typed-source runtime execution entry point. -/

#check Solcore.Frontend.SourceTypedRuntime.Value
#check Solcore.Frontend.SourceTypedRuntime.RunResult
#check Solcore.Frontend.SourceTypedRuntime.Value.type?
#check Solcore.Frontend.SourceTypedRuntime.Value.validateTypeFuel
#check Solcore.Frontend.SourceTypedRuntime.validateInputs

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.runTrusted
#check_failure Solcore.Frontend.SourceTypedRuntime.runWithValidationFuel
#check_failure Solcore.Frontend.SourceTypedRuntime.invokeSpecialization
#check_failure Solcore.Frontend.SourceTypedRuntime.evaluateExpression
#check_failure Solcore.Frontend.SourceTypedRuntime.executeStatement
end
