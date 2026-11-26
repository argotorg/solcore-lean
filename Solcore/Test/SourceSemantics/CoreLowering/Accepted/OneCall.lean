import Solcore.Test.SourceSemantics.CoreLowering.Accepted.Fixture
import Solcore.Test.SourceSemantics.CoreLowering.Direct.Calls
import Solcore.Test.SourceSemantics.CoreLowering.Builtin

/-!
# Direct calls and a conversion at the accepted-body public root

`relay` returns `identity(value)`, a direct call of the program's first
function, and `twice` returns `identity(identity(value))`, a direct call whose
argument is another direct call, both at a `Word` parameter; `narrow` returns
`uint8(value)`, a conversion of its `Word` parameter, and `roundTrip` returns
`Typedef.rep(uint8(value))`, the word of that value; `doubled` converts its
parameter to a `uint8` local `x`, adds `x` to it in place and returns it, `shifted` shifts such
an `x` left in place by the parameter, a `Word` amount, and `flipped` applies `~` to such an `x` in
place; `tailed`'s body is `identity(value)` as its final value; `stored` declares a local mapping
`table`, assigns its parameter at `table[value]` and returns `table[value]`; `summed` returns
`integerAdd(wordToInteger(value), wordToInteger(value))`, calls of builtin closures, `zeroed`
returns `iszero(value)`, the opcode that the program imports from `std.opcodes`, `inverted`
declares a local mapping, complements `table[value]` in place and returns it, `broken` runs
`while (true) { break; }` before it returns its parameter, and `counted` runs
`for (let go: bool = true; go; go = false) { continue; }` before it does, `tripled` returns
`(value, value, value)`, a tuple beyond pairs, and `boxed` returns `.Item(value)`, an application of
the constructor of the program's enum `Box`. Runtime checks place
every expression node of the twenty-three rows among the nested sites that call `identity`'s
instantiation or their callees, and each statement list in the supported
shape. With the complete inventory the rows make a family and give
the admitted callee's static receipts. The original Source executions of
`relay`, `twice`, `tailed`, `stored`, `summed`, `zeroed`, `inverted`, `broken`, `counted`, `tripled`,
`boxed`, `narrow` and `roundTrip` (at words canonical for `uint8`) are lifted to staged traces, and the call root's theorems apply at the first public call of
each in both directions: the actual resumption succeeds, and actual native
completion reconstructs a staged Source execution. `stored`'s index read returns the word its
assignment wrote, not the default, and `summed` returns its integer, which at the largest word
exceeds every word. At other words the call
root's reflection applies to `narrow` and `roundTrip`, and the actual
resumption fails with the dirty-integer reason. At every word the call root's
reflection applies to `doubled`: below 128 the actual resumption returns the sum,
from 128 the checked `+=` panics with `0x11`, and at a word outside `uint8` the
conversion fails with the dirty-integer reason. So does it to `shifted`: at a word in `uint8` the
actual resumption returns Word's shift wrapped to eight bits, and at any other word the conversion
fails. So does it to `flipped`: at a word in `uint8` the actual resumption returns its complement in
eight bits, and at any other word the conversion fails. At the faulting words of `narrow`, `doubled`,
`shifted` and `flipped` the row's original Source execution faults, its staged fault trace is lifted
from it, and the call root's failure theorem applies: the actual resumption fails with a token that
represents the Source fault.

Of the memory array rows, `filled` returns the length of `new Word[](uint256(value))`, `listed` the element of
`[value, value, value]` at `value`, `sliced` the element of the slice `[value, value, value][uint256(value):]`
at `value`, `copied` the element of `toArray([value, value, value][:])` at `value`, `referenced` stores its
parameter through `lidx(a, value)` into its local `a`, the literal `[value, value, value]`, and returns
`CanStore.load(lidx(a, value))`, and `bumped` writes `a[value]` of such a local by `a[value] = value`,
`a[value] += value` and `a[value] ~=;` and returns it. The call root's reflection applies to them at every word:
from `2^251 − 1` `new` panics with `0x41`; a read outside its array or slice, a slice's start outside its array,
or a memref's or a write's index outside its array panics with `0x32`.

Main declarations: `Tests.SourceCoreAcceptedOneCall.relay_source`,
`Tests.SourceCoreAcceptedOneCall.twice_source`,
`Tests.SourceCoreAcceptedOneCall.tailed_source`,
`Tests.SourceCoreAcceptedOneCall.stored_source`,
`Tests.SourceCoreAcceptedOneCall.summed_source`,
`Tests.SourceCoreAcceptedOneCall.zeroed_source`,
`Tests.SourceCoreAcceptedOneCall.inverted_source`,
`Tests.SourceCoreAcceptedOneCall.broken_source`,
`Tests.SourceCoreAcceptedOneCall.counted_source`,
`Tests.SourceCoreAcceptedOneCall.tripled_source`,
`Tests.SourceCoreAcceptedOneCall.boxed_source`,
`Tests.SourceCoreAcceptedOneCall.narrow_source`,
`Tests.SourceCoreAcceptedOneCall.roundTrip_source`,
`Tests.SourceCoreAcceptedOneCall.narrow_fault`,
`Tests.SourceCoreAcceptedOneCall.initializer_fault`,
`Tests.SourceCoreAcceptedOneCall.doubled_panic`,
`Tests.SourceCoreAcceptedOneCall.accepted_call`,
`Tests.SourceCoreAcceptedOneCall.accepted_call_with_locals`,
`Tests.SourceCoreAcceptedOneCall.accepted_call_returning`,
`Tests.SourceCoreAcceptedOneCall.accepted_reflection`,
`Tests.SourceCoreAcceptedOneCall.accepted_failure` and the runtime checks
`Tests.SourceCoreAcceptedOneCall.AcceptedCallRuntime.run`,
`Tests.SourceCoreAcceptedOneCall.AcceptedNestedCallRuntime.run`,
`Tests.SourceCoreAcceptedOneCall.AcceptedTailRuntime.run`,
`Tests.SourceCoreAcceptedOneCall.AcceptedMappingRuntime.run`,
`Tests.SourceCoreAcceptedOneCall.AcceptedBuiltinRuntime.run`,
`Tests.SourceCoreAcceptedOneCall.AcceptedOpcodeRuntime.run`,
`Tests.SourceCoreAcceptedOneCall.AcceptedProjectedBitNotRuntime.run`,
`Tests.SourceCoreAcceptedOneCall.AcceptedLoopRuntime.run`,
`Tests.SourceCoreAcceptedOneCall.AcceptedTupleRuntime.run`,
`Tests.SourceCoreAcceptedOneCall.AcceptedConstructorRuntime.run`,
`Tests.SourceCoreAcceptedOneCall.AcceptedConversionRuntime.run`,
`Tests.SourceCoreAcceptedOneCall.AcceptedRepresentationRuntime.run`,
`Tests.SourceCoreAcceptedOneCall.AcceptedFixedCompoundRuntime.run`,
`Tests.SourceCoreAcceptedOneCall.AcceptedFixedShiftRuntime.run`,
`Tests.SourceCoreAcceptedOneCall.AcceptedFixedBitNotRuntime.run`,
`Tests.SourceCoreAcceptedOneCall.AcceptedFaultRuntime.run` and
`Tests.SourceCoreAcceptedOneCall.AcceptedArrayRuntime.run`.
-/

section
/-! The program and the declarative typing of its twenty-three functions, constructed
from checked source observations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreAcceptedOneCall
open Solcore Frontend SourceInference SourceSemantics
open Tests.SourceCoreAcceptedFixture (observed)

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "pragma solcore;",
    "import { iszero } from std.opcodes;",
    "function identity(value: word) returns (word) { return value; }",
    "function relay(value: word) returns (word) { return identity(value); }",
    "function twice(value: word) returns (word) { return identity(identity(value)); }",
    "function narrow(value: word) returns (uint8) { return uint8(value); }",
    "function roundTrip(value: word) returns (word) { return Typedef.rep(uint8(value)); }",
    "function doubled(value: word) returns (uint8) { let x: uint8 = uint8(value); x += x; return x; }",
    "function shifted(value: word) returns (uint8) { let x: uint8 = uint8(value); x <<= value; return x; }",
    "function flipped(value: word) returns (uint8) { let x: uint8 = uint8(value); x ~=; return x; }",
    "function tailed(value: word) returns (word) { identity(value) }",
    "function stored(value: word) returns (word) { let table: mapping(word => word); table[value] = value; " ++
      "return table[value]; }",
    "function summed(value: word) returns (integer) { " ++
      "return integerAdd(wordToInteger(value), wordToInteger(value)); }",
    "function zeroed(value: word) returns (word) { return iszero(value); }",
    "function inverted(value: word) returns (word) { let table: mapping(word => word); table[value] ~=; " ++
      "return table[value]; }",
    "function broken(value: word) returns (word) { while (true) { break; } return value; }",
    "function counted(value: word) returns (word) { for (let go: bool = true; go; go = false) { continue; } " ++
      "return value; }",
    "function tripled(value: word) returns ((word, word, word)) { return (value, value, value); }",
    "enum Box { Item(word) }",
    "function boxed(value: word) returns (Box) { return .Item(value); }",
    "function filled(value: word) returns (uint256) { return Length.length(new word[](uint256(value))); }",
    "function listed(value: word) returns (word) { return [value, value, value][value]; }",
    "function sliced(value: word) returns (word) { return [value, value, value][uint256(value):][value]; }",
    "function copied(value: word) returns (word) { return toArray([value, value, value][:])[value]; }",
    "function referenced(value: word) returns (word) { let a: word[] = [value, value, value]; " ++
      "CanStore.store(lidx(a, value), value); return CanStore.load(lidx(a, value)); }",
    "function bumped(value: word) returns (word) { let a: word[] = [value, value, value]; a[value] = value; " ++
      "a[value] += value; a[value] ~=; return a[value]; }" ]}] }

def options : SourceCoreCompiler.Options :=
  {checkingFuel := 1000, compilationFuel := 1000, specializationBudget := 128}

private theorem statementRoots_injective {left right : List StatementId}
    (equal : left.map NodeId.statement = right.map NodeId.statement) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp at equal ⊢
  | cons head rest ih =>
    cases right with
    | nil => simp at equal
    | cons other tail =>
      simp only [List.map_cons, List.cons.injEq] at equal
      obtain ⟨same, tails⟩ := equal
      cases same
      simp only [ih tails]

/-- `relay`'s body: the read of its parameter, the direct call of `identity`
with it and the return of the call. -/
structure RelayShape (function : CheckedFunction) (signature identity : ProgramFunctionSignature) where
  binder : TypedBinder
  read : Tests.SourceCoreNamedBranch.Read function.typedBody binder .word
  call : Tests.SourceCoreDirectCalls.DirectCall function.typedBody identity read.node.id .word
  statement : StatementNode
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [.word]
  inputs : function.typedBody.inputs = [binder]
  binderScheme : binder.scheme = .mono .word
  binderRequirements : binder.schemeRequirements = []
  binderOrdinary : binder.comptime = false
  roots : function.typedBody.roots = [.statement statement.id]
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some call.value.node.id)
  statementType : statement.type = .word

/-- `twice`'s body: the read of its parameter, the direct call of `identity`
with it, the direct call of `identity` with that call and the return of the
outer call. -/
structure TwiceShape (function : CheckedFunction) (signature identity : ProgramFunctionSignature) where
  binder : TypedBinder
  read : Tests.SourceCoreNamedBranch.Read function.typedBody binder .word
  inner : Tests.SourceCoreDirectCalls.DirectCall function.typedBody identity read.node.id .word
  outer : Tests.SourceCoreDirectCalls.DirectCall function.typedBody identity inner.value.node.id .word
  statement : StatementNode
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [.word]
  inputs : function.typedBody.inputs = [binder]
  binderScheme : binder.scheme = .mono .word
  binderRequirements : binder.schemeRequirements = []
  binderOrdinary : binder.comptime = false
  roots : function.typedBody.roots = [.statement statement.id]
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some outer.value.node.id)
  statementType : statement.type = .word

theorem RelayShape.statementTyping {function : CheckedFunction} {signature identity : ProgramFunctionSignature}
    (shape : RelayShape function signature identity) (signatures : ProgramSignatures)
    (identityMember : identity ∈ signatures.functions) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.statement.id] := statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type := .word, hasValue := true, sawReturn := true, control := .returned}
  refine ⟨BodyFacts.singleton facts, rfl, ?_⟩
  intro lexical extension
  rw [shape.inputs, shape.inputTypes] at extension
  cases extension with
  | cons scheme head tail =>
    cases tail
    have binders : TypeParameterBindersWellFormed lexical := by
      rw [TypeParameterBindersWellFormed, head.context_fields.2.2.1]
      simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
        Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
    have fields : lexical.signatures = signatures := by
      rw [head.context_fields.1]
      rfl
    have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
    have read := shape.read.typed scheme shape.binderRequirements word head.local_self head.local_scheme_requirements_self
    have called := shape.call.typed (fields ▸ identityMember) word read
    exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.statementFound)
      shape.statementForm called shape.statementType)⟩

theorem TwiceShape.statementTyping {function : CheckedFunction} {signature identity : ProgramFunctionSignature}
    (shape : TwiceShape function signature identity) (signatures : ProgramSignatures)
    (identityMember : identity ∈ signatures.functions) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.statement.id] := statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type := .word, hasValue := true, sawReturn := true, control := .returned}
  refine ⟨BodyFacts.singleton facts, rfl, ?_⟩
  intro lexical extension
  rw [shape.inputs, shape.inputTypes] at extension
  cases extension with
  | cons scheme head tail =>
    cases tail
    have binders : TypeParameterBindersWellFormed lexical := by
      rw [TypeParameterBindersWellFormed, head.context_fields.2.2.1]
      simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
        Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
    have fields : lexical.signatures = signatures := by
      rw [head.context_fields.1]
      rfl
    have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
    have read := shape.read.typed scheme shape.binderRequirements word head.local_self head.local_scheme_requirements_self
    have inner := shape.inner.typed (fields ▸ identityMember) word read
    have outer := shape.outer.typed (fields ▸ identityMember) word inner
    exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.statementFound)
      shape.statementForm outer shape.statementType)⟩

def observeRelay (function : CheckedFunction) (signature identity : ProgramFunctionSignature) :
    IO (RelayShape function signature identity) := do
  let [binder] := function.typedBody.inputs | throw (IO.userError "relay input")
  let [.expression read, .expression callee, .expression value, .statement statement] := function.typedBody.nodes
    | throw (IO.userError "relay original nodes")
  let read ← Tests.SourceCoreNamedBranch.observeRead function.typedBody binder read .word
  let call ← Tests.SourceCoreDirectCalls.observeDirect function.typedBody identity read.node.id callee value .word
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "relay parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "relay inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.word]) "relay returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [binder]) "relay inputs"
  let ⟨binderScheme⟩ ← observed (binder.scheme = .mono .word) "relay binderScheme"
  let ⟨binderRequirements⟩ ← observed (binder.schemeRequirements = []) "relay binderRequirements"
  let ⟨binderOrdinary⟩ ← observed (binder.comptime = false) "relay binderOrdinary"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "relay roots"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement)
    "relay statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some call.value.node.id)) "relay statementForm"
  let ⟨statementType⟩ ← observed (statement.type = .word) "relay statementType"
  return ⟨binder, read, call, statement, parameters, inputTypes, returns, inputs, binderScheme, binderRequirements,
    binderOrdinary, roots, statementFound, statementForm, statementType⟩

/-- `tailed`'s body: the read of its parameter, the direct call of `identity`
with it, and the call as the body's final value. -/
structure TailedShape (function : CheckedFunction) (signature identity : ProgramFunctionSignature) where
  binder : TypedBinder
  read : Tests.SourceCoreNamedBranch.Read function.typedBody binder .word
  call : Tests.SourceCoreDirectCalls.DirectCall function.typedBody identity read.node.id .word
  statement : StatementNode
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [.word]
  inputs : function.typedBody.inputs = [binder]
  binderScheme : binder.scheme = .mono .word
  binderRequirements : binder.schemeRequirements = []
  binderOrdinary : binder.comptime = false
  roots : function.typedBody.roots = [.statement statement.id]
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .expression call.value.node.id false
  statementType : statement.type = .word

theorem TailedShape.statementTyping {function : CheckedFunction} {signature identity : ProgramFunctionSignature}
    (shape : TailedShape function signature identity) (signatures : ProgramSignatures)
    (identityMember : identity ∈ signatures.functions) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.statement.id] := statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type := .word, hasValue := true, sawReturn := false, control := .ordinary .word}
  refine ⟨BodyFacts.singleton facts, rfl, ?_⟩
  intro lexical extension
  rw [shape.inputs, shape.inputTypes] at extension
  cases extension with
  | cons scheme head tail =>
    cases tail
    have binders : TypeParameterBindersWellFormed lexical := by
      rw [TypeParameterBindersWellFormed, head.context_fields.2.2.1]
      simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
        Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
    have fields : lexical.signatures = signatures := by
      rw [head.context_fields.1]
      rfl
    have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
    have read := shape.read.typed scheme shape.binderRequirements word head.local_self head.local_scheme_requirements_self
    have called := shape.call.typed (fields ▸ identityMember) word read
    exact ⟨_, .singleton (.expressionValue (lookupStatement?_sound shape.statementFound)
      shape.statementForm called shape.statementType)⟩

def observeTailed (function : CheckedFunction) (signature identity : ProgramFunctionSignature) :
    IO (TailedShape function signature identity) := do
  let [binder] := function.typedBody.inputs | throw (IO.userError "tailed input")
  let [.statement statementId] := function.typedBody.roots | throw (IO.userError "tailed roots")
  let some statement := function.typedBody.lookupStatement? statementId | throw (IO.userError "tailed statement")
  let .expression valueId false := statement.form | throw (IO.userError "tailed final value")
  let some valueNode := function.typedBody.lookupExpression? valueId | throw (IO.userError "tailed call node")
  let .call calleeId [readId] _ := valueNode.form | throw (IO.userError "tailed call form")
  let some calleeNode := function.typedBody.lookupExpression? calleeId | throw (IO.userError "tailed callee")
  let some readNode := function.typedBody.lookupExpression? readId | throw (IO.userError "tailed read")
  let read ← Tests.SourceCoreNamedBranch.observeRead function.typedBody binder readNode .word
  let call ← Tests.SourceCoreDirectCalls.observeDirect function.typedBody identity read.node.id calleeNode valueNode
    .word
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "tailed parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "tailed inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.word]) "tailed returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [binder]) "tailed inputs"
  let ⟨binderScheme⟩ ← observed (binder.scheme = .mono .word) "tailed binderScheme"
  let ⟨binderRequirements⟩ ← observed (binder.schemeRequirements = []) "tailed binderRequirements"
  let ⟨binderOrdinary⟩ ← observed (binder.comptime = false) "tailed binderOrdinary"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "tailed roots shape"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement)
    "tailed statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .expression call.value.node.id false) "tailed statementForm"
  let ⟨statementType⟩ ← observed (statement.type = .word) "tailed statementType"
  return ⟨binder, read, call, statement, parameters, inputTypes, returns, inputs, binderScheme, binderRequirements,
    binderOrdinary, roots, statementFound, statementForm, statementType⟩

/-- The nodes of a body that returns `identity(identity(value))`, found by
following the return statement's expression graph. -/
structure TwiceParts (source : TypedSource) (identity : ProgramFunctionSignature) where
  binder : TypedBinder
  read : Tests.SourceCoreNamedBranch.Read source binder .word
  inner : Tests.SourceCoreDirectCalls.DirectCall source identity read.node.id .word
  outer : Tests.SourceCoreDirectCalls.DirectCall source identity inner.value.node.id .word
  statement : StatementNode
  inputs : source.inputs = [binder]
  roots : source.roots = [.statement statement.id]
  statementFound : source.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some outer.value.node.id)

def observeTwiceParts (source : TypedSource) (identity : ProgramFunctionSignature) :
    IO (TwiceParts source identity) := do
  let [binder] := source.inputs | throw (IO.userError "twice input")
  let [.statement statementId] := source.roots | throw (IO.userError "twice roots")
  let some statement := source.lookupStatement? statementId | throw (IO.userError "twice statement")
  let .returnStmt (some outerId) := statement.form | throw (IO.userError "twice return")
  let some outerNode := source.lookupExpression? outerId | throw (IO.userError "twice outer call")
  let .call outerCalleeId [innerId] _ := outerNode.form | throw (IO.userError "twice outer form")
  let some outerCallee := source.lookupExpression? outerCalleeId | throw (IO.userError "twice outer callee")
  let some innerNode := source.lookupExpression? innerId | throw (IO.userError "twice inner call")
  let .call innerCalleeId [readId] _ := innerNode.form | throw (IO.userError "twice inner form")
  let some innerCallee := source.lookupExpression? innerCalleeId | throw (IO.userError "twice inner callee")
  let some readNode := source.lookupExpression? readId | throw (IO.userError "twice read")
  let read ← Tests.SourceCoreNamedBranch.observeRead source binder readNode .word
  let inner ← Tests.SourceCoreDirectCalls.observeDirect source identity read.node.id innerCallee innerNode .word
  let outer ← Tests.SourceCoreDirectCalls.observeDirect source identity inner.value.node.id outerCallee outerNode .word
  let ⟨inputs⟩ ← observed (source.inputs = [binder]) "twice inputs"
  let ⟨roots⟩ ← observed (source.roots = [.statement statement.id]) "twice roots shape"
  let ⟨statementFound⟩ ← observed (source.lookupStatement? statement.id = some statement) "twice statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some outer.value.node.id)) "twice statementForm"
  return ⟨binder, read, inner, outer, statement, inputs, roots, statementFound, statementForm⟩

def observeTwice (function : CheckedFunction) (signature identity : ProgramFunctionSignature) :
    IO (TwiceShape function signature identity) := do
  let parts ← observeTwiceParts function.typedBody identity
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "twice parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "twice inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.word]) "twice returns"
  let ⟨binderScheme⟩ ← observed (parts.binder.scheme = .mono .word) "twice binderScheme"
  let ⟨binderRequirements⟩ ← observed (parts.binder.schemeRequirements = []) "twice binderRequirements"
  let ⟨binderOrdinary⟩ ← observed (parts.binder.comptime = false) "twice binderOrdinary"
  let ⟨statementType⟩ ← observed (parts.statement.type = .word) "twice statementType"
  return ⟨parts.binder, parts.read, parts.inner, parts.outer, parts.statement, parameters, inputTypes, returns,
    parts.inputs, binderScheme, binderRequirements, binderOrdinary, parts.roots, parts.statementFound,
    parts.statementForm, statementType⟩

/-- The nodes of a body that returns `uint8(value)`, found by following the
return statement's expression graph. -/
structure NarrowParts (source : TypedSource) where
  binder : TypedBinder
  read : Tests.SourceCoreNamedBranch.Read source binder .word
  converted : Tests.SourceCoreBuiltinCalls.BuiltinCall source (.fixedFromWord ⟨false, .w8⟩) read.node.id
  statement : StatementNode
  inputs : source.inputs = [binder]
  roots : source.roots = [.statement statement.id]
  statementFound : source.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some converted.value.node.id)

/-- A conversion `function(argument)`, from its actual callee and call nodes. -/
def observeConversion (source : TypedSource) (function : BuiltinFunctionId) (argument : ExpressionId)
    (calleeNode valueNode : ExpressionNode) :
    IO (Tests.SourceCoreBuiltinCalls.BuiltinCall source function argument) := do
  let callee ← Tests.SourceCoreOperatorCalls.observeNode source calleeNode function.type
  let value ← Tests.SourceCoreOperatorCalls.observeNode source valueNode function.returnType
  let .reference name (.builtinFunction _) := calleeNode.form | throw (IO.userError "conversion callee form")
  let ⟨calleeForm⟩ ← observed (callee.node.form = .reference name (.builtinFunction function)) "conversion callee"
  let ⟨form⟩ ← observed (value.node.form = .call callee.node.id [argument] (.builtinFunction function))
    "conversion call"
  return {callee, value, name, calleeForm, form}

def observeNarrowParts (source : TypedSource) : IO (NarrowParts source) := do
  let [binder] := source.inputs | throw (IO.userError "narrow input")
  let [.statement statementId] := source.roots | throw (IO.userError "narrow roots")
  let some statement := source.lookupStatement? statementId | throw (IO.userError "narrow statement")
  let .returnStmt (some valueId) := statement.form | throw (IO.userError "narrow return")
  let some valueNode := source.lookupExpression? valueId | throw (IO.userError "narrow conversion node")
  let .call calleeId [readId] _ := valueNode.form | throw (IO.userError "narrow conversion form")
  let some calleeNode := source.lookupExpression? calleeId | throw (IO.userError "narrow callee")
  let some readNode := source.lookupExpression? readId | throw (IO.userError "narrow read")
  let read ← Tests.SourceCoreNamedBranch.observeRead source binder readNode .word
  let converted ← observeConversion source (.fixedFromWord ⟨false, .w8⟩) read.node.id calleeNode valueNode
  let ⟨inputs⟩ ← observed (source.inputs = [binder]) "narrow inputs"
  let ⟨roots⟩ ← observed (source.roots = [.statement statement.id]) "narrow roots shape"
  let ⟨statementFound⟩ ← observed (source.lookupStatement? statement.id = some statement) "narrow statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some converted.value.node.id))
    "narrow statementForm"
  return ⟨binder, read, converted, statement, inputs, roots, statementFound, statementForm⟩

/-- `narrow`'s body: the read of its parameter, its conversion `uint8(value)`
and the return of the conversion. -/
structure NarrowShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  parts : NarrowParts function.typedBody
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [.fixed ⟨false, .w8⟩]
  binderScheme : parts.binder.scheme = .mono .word
  binderRequirements : parts.binder.schemeRequirements = []
  binderOrdinary : parts.binder.comptime = false
  statementType : parts.statement.type = .fixed ⟨false, .w8⟩

theorem NarrowShape.statementTyping {function : CheckedFunction} {signature : ProgramFunctionSignature}
    (shape : NarrowShape function signature) (signatures : ProgramSignatures) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.parts.statement.id] :=
    statementRoots_injective (roots.symm.trans shape.parts.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts :=
    {type := .fixed ⟨false, .w8⟩, hasValue := true, sawReturn := true, control := .returned}
  refine ⟨BodyFacts.singleton facts, rfl, ?_⟩
  intro lexical extension
  rw [shape.parts.inputs, shape.inputTypes] at extension
  cases extension with
  | cons scheme head tail =>
    cases tail
    have binders : TypeParameterBindersWellFormed lexical := by
      rw [TypeParameterBindersWellFormed, head.context_fields.2.2.1]
      simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
        Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
    have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
    have narrow : TypeAdmissible lexical (.fixed ⟨false, .w8⟩) := ⟨binders, .builtin (.fixed ⟨false, .w8⟩)⟩
    have read := shape.parts.read.typed scheme shape.binderRequirements word head.local_self
      head.local_scheme_requirements_self
    have converted := shape.parts.converted.typed rfl narrow read
    exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.parts.statementFound)
      shape.parts.statementForm converted shape.statementType)⟩

def observeNarrow (function : CheckedFunction) (signature : ProgramFunctionSignature) :
    IO (NarrowShape function signature) := do
  let parts ← observeNarrowParts function.typedBody
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "narrow parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "narrow inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.fixed ⟨false, .w8⟩]) "narrow returns"
  let ⟨binderScheme⟩ ← observed (parts.binder.scheme = .mono .word) "narrow binderScheme"
  let ⟨binderRequirements⟩ ← observed (parts.binder.schemeRequirements = []) "narrow binderRequirements"
  let ⟨binderOrdinary⟩ ← observed (parts.binder.comptime = false) "narrow binderOrdinary"
  let ⟨statementType⟩ ← observed (parts.statement.type = .fixed ⟨false, .w8⟩) "narrow statementType"
  return ⟨parts, parameters, inputTypes, returns, binderScheme, binderRequirements, binderOrdinary,
    statementType⟩

/-- The nodes of a body that returns `Typedef.rep(uint8(value))`, found by
following the return statement's expression graph. -/
structure RoundTripParts (source : TypedSource) where
  binder : TypedBinder
  read : Tests.SourceCoreNamedBranch.Read source binder .word
  narrowed : Tests.SourceCoreBuiltinCalls.BuiltinCall source (.fixedFromWord ⟨false, .w8⟩) read.node.id
  represented : Tests.SourceCoreBuiltinCalls.BuiltinCall source (.fixedToWord ⟨false, .w8⟩) narrowed.value.node.id
  statement : StatementNode
  inputs : source.inputs = [binder]
  roots : source.roots = [.statement statement.id]
  statementFound : source.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some represented.value.node.id)

def observeRoundTripParts (source : TypedSource) : IO (RoundTripParts source) := do
  let [binder] := source.inputs | throw (IO.userError "roundTrip input")
  let [.statement statementId] := source.roots | throw (IO.userError "roundTrip roots")
  let some statement := source.lookupStatement? statementId | throw (IO.userError "roundTrip statement")
  let .returnStmt (some outerId) := statement.form | throw (IO.userError "roundTrip return")
  let some outerNode := source.lookupExpression? outerId | throw (IO.userError "roundTrip outer node")
  let .call outerCalleeId [innerId] _ := outerNode.form | throw (IO.userError "roundTrip outer form")
  let some outerCallee := source.lookupExpression? outerCalleeId | throw (IO.userError "roundTrip outer callee")
  let some innerNode := source.lookupExpression? innerId | throw (IO.userError "roundTrip inner node")
  let .call innerCalleeId [readId] _ := innerNode.form | throw (IO.userError "roundTrip inner form")
  let some innerCallee := source.lookupExpression? innerCalleeId | throw (IO.userError "roundTrip inner callee")
  let some readNode := source.lookupExpression? readId | throw (IO.userError "roundTrip read")
  let read ← Tests.SourceCoreNamedBranch.observeRead source binder readNode .word
  let narrowed ← observeConversion source (.fixedFromWord ⟨false, .w8⟩) read.node.id innerCallee innerNode
  let represented ← observeConversion source (.fixedToWord ⟨false, .w8⟩) narrowed.value.node.id outerCallee outerNode
  let ⟨inputs⟩ ← observed (source.inputs = [binder]) "roundTrip inputs"
  let ⟨roots⟩ ← observed (source.roots = [.statement statement.id]) "roundTrip roots shape"
  let ⟨statementFound⟩ ← observed (source.lookupStatement? statement.id = some statement)
    "roundTrip statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some represented.value.node.id))
    "roundTrip statementForm"
  return ⟨binder, read, narrowed, represented, statement, inputs, roots, statementFound, statementForm⟩

/-- `roundTrip`'s body: the read of its parameter, its conversion to `uint8`,
`Typedef.rep` of that value and the return of it. -/
structure RoundTripShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  parts : RoundTripParts function.typedBody
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [.word]
  binderScheme : parts.binder.scheme = .mono .word
  binderRequirements : parts.binder.schemeRequirements = []
  binderOrdinary : parts.binder.comptime = false
  statementType : parts.statement.type = .word

theorem RoundTripShape.statementTyping {function : CheckedFunction} {signature : ProgramFunctionSignature}
    (shape : RoundTripShape function signature) (signatures : ProgramSignatures) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.parts.statement.id] :=
    statementRoots_injective (roots.symm.trans shape.parts.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type := .word, hasValue := true, sawReturn := true, control := .returned}
  refine ⟨BodyFacts.singleton facts, rfl, ?_⟩
  intro lexical extension
  rw [shape.parts.inputs, shape.inputTypes] at extension
  cases extension with
  | cons scheme head tail =>
    cases tail
    have binders : TypeParameterBindersWellFormed lexical := by
      rw [TypeParameterBindersWellFormed, head.context_fields.2.2.1]
      simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
        Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
    have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
    have narrow : TypeAdmissible lexical (.fixed ⟨false, .w8⟩) := ⟨binders, .builtin (.fixed ⟨false, .w8⟩)⟩
    have read := shape.parts.read.typed scheme shape.binderRequirements word head.local_self
      head.local_scheme_requirements_self
    have narrowed := shape.parts.narrowed.typed rfl narrow read
    have represented := shape.parts.represented.typed rfl word narrowed
    exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.parts.statementFound)
      shape.parts.statementForm represented shape.statementType)⟩

def observeRoundTrip (function : CheckedFunction) (signature : ProgramFunctionSignature) :
    IO (RoundTripShape function signature) := do
  let parts ← observeRoundTripParts function.typedBody
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "roundTrip parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "roundTrip inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.word]) "roundTrip returns"
  let ⟨binderScheme⟩ ← observed (parts.binder.scheme = .mono .word) "roundTrip binderScheme"
  let ⟨binderRequirements⟩ ← observed (parts.binder.schemeRequirements = []) "roundTrip binderRequirements"
  let ⟨binderOrdinary⟩ ← observed (parts.binder.comptime = false) "roundTrip binderOrdinary"
  let ⟨statementType⟩ ← observed (parts.statement.type = .word) "roundTrip statementType"
  return ⟨parts, parameters, inputTypes, returns, binderScheme, binderRequirements, binderOrdinary,
    statementType⟩

/-- The nodes of `doubled`'s body: the read of its parameter, `uint8(value)` initializing the local
`x`, `x += x` and the return of `x`, found by following the statement graph. -/
structure DoubledParts (source : TypedSource) where
  binder : TypedBinder
  target : TypedBinder
  read : Tests.SourceCoreNamedBranch.Read source binder .word
  converted : Tests.SourceCoreBuiltinCalls.BuiltinCall source (.fixedFromWord ⟨false, .w8⟩) read.node.id
  rightRead : Tests.SourceCoreNamedBranch.Read source target (.fixed ⟨false, .w8⟩)
  returnRead : Tests.SourceCoreNamedBranch.Read source target (.fixed ⟨false, .w8⟩)
  initialized : StatementNode
  assignment : StatementNode
  resolution : AssignmentResolution
  returned : StatementNode
  inputs : source.inputs = [binder]
  roots : source.roots = [.statement initialized.id, .statement assignment.id, .statement returned.id]
  initializedFound : source.lookupStatement? initialized.id = some initialized
  initializedForm : initialized.form = .letDecl target (some converted.value.node.id)
  assignmentFound : source.lookupStatement? assignment.id = some assignment
  assignmentForm : assignment.form = .assignValue resolution .add rightRead.node.id
  returnedFound : source.lookupStatement? returned.id = some returned
  returnedForm : returned.form = .returnStmt (some returnRead.node.id)

def observeDoubledParts (source : TypedSource) : IO (DoubledParts source) := do
  let [binder] := source.inputs | throw (IO.userError "doubled input")
  let [.statement initializedId, .statement assignmentId, .statement returnedId] := source.roots
    | throw (IO.userError "doubled roots")
  let some initialized := source.lookupStatement? initializedId | throw (IO.userError "doubled let")
  let some assignment := source.lookupStatement? assignmentId | throw (IO.userError "doubled assignment")
  let some returned := source.lookupStatement? returnedId | throw (IO.userError "doubled return")
  let .letDecl target (some valueId) := initialized.form | throw (IO.userError "doubled let form")
  let .assignValue resolution .add rightId := assignment.form | throw (IO.userError "doubled assignment form")
  let .returnStmt (some returnId) := returned.form | throw (IO.userError "doubled return form")
  let some valueNode := source.lookupExpression? valueId | throw (IO.userError "doubled conversion node")
  let .call calleeId [readId] _ := valueNode.form | throw (IO.userError "doubled conversion form")
  let some calleeNode := source.lookupExpression? calleeId | throw (IO.userError "doubled callee")
  let some readNode := source.lookupExpression? readId | throw (IO.userError "doubled read")
  let some rightNode := source.lookupExpression? rightId | throw (IO.userError "doubled right read")
  let some returnNode := source.lookupExpression? returnId | throw (IO.userError "doubled returned read")
  let read ← Tests.SourceCoreNamedBranch.observeRead source binder readNode .word
  let converted ← observeConversion source (.fixedFromWord ⟨false, .w8⟩) read.node.id calleeNode valueNode
  let rightRead ← Tests.SourceCoreNamedBranch.observeRead source target rightNode (.fixed ⟨false, .w8⟩)
  let returnRead ← Tests.SourceCoreNamedBranch.observeRead source target returnNode (.fixed ⟨false, .w8⟩)
  let ⟨inputs⟩ ← observed (source.inputs = [binder]) "doubled inputs"
  let ⟨roots⟩ ← observed (source.roots = [.statement initialized.id, .statement assignment.id, .statement returned.id])
    "doubled roots shape"
  let ⟨initializedFound⟩ ← observed (source.lookupStatement? initialized.id = some initialized) "doubled initializedFound"
  let ⟨initializedForm⟩ ← observed (initialized.form = .letDecl target (some converted.value.node.id))
    "doubled initializedForm"
  let ⟨assignmentFound⟩ ← observed (source.lookupStatement? assignment.id = some assignment) "doubled assignmentFound"
  let ⟨assignmentForm⟩ ← observed (assignment.form = .assignValue resolution .add rightRead.node.id)
    "doubled assignmentForm"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "doubled returnedFound"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some returnRead.node.id)) "doubled returnedForm"
  return ⟨binder, target, read, converted, rightRead, returnRead, initialized, assignment, resolution, returned,
    inputs, roots, initializedFound, initializedForm, assignmentFound, assignmentForm, returnedFound, returnedForm⟩

/-- `doubled`'s body: `let x: uint8 = uint8(value)`, the checked `x += x` at the fixed-width local and
the return of `x`. -/
structure DoubledShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  parts : DoubledParts function.typedBody
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [.fixed ⟨false, .w8⟩]
  binderScheme : parts.binder.scheme = .mono .word
  binderRequirements : parts.binder.schemeRequirements = []
  targetScheme : parts.target.scheme = .mono (.fixed ⟨false, .w8⟩)
  targetRequirements : parts.target.schemeRequirements = []
  targetOwner : parts.target.id.owner = function.typedBody.owner
  targetDistinct : parts.target.id ≠ parts.binder.id
  targetOrdinary : parts.target.comptime = false
  initializedType : parts.initialized.type = .unit
  assignmentType : parts.assignment.type = .unit
  returnedType : parts.returned.type = .fixed ⟨false, .w8⟩
  targetRoot : parts.resolution.target.root = parts.target.id
  targetType : parts.resolution.target.type = .fixed ⟨false, .w8⟩
  targetBare : parts.resolution.target.projections = []
  assignmentRequirements : parts.resolution.requirements = []

theorem DoubledShape.statementTyping {function : CheckedFunction} {signature : ProgramFunctionSignature}
    (shape : DoubledShape function signature) (signatures : ProgramSignatures) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.parts.initialized.id, shape.parts.assignment.id, shape.parts.returned.id] :=
    statementRoots_injective (roots.symm.trans shape.parts.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts :=
    {type := .fixed ⟨false, .w8⟩, hasValue := true, sawReturn := true, control := .returned}
  let ordinary : StatementFacts := {type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit}
  refine ⟨BodyFacts.cons ordinary (BodyFacts.cons ordinary (BodyFacts.singleton facts)), rfl, ?_⟩
  intro lexical extension
  rw [shape.parts.inputs, shape.inputTypes] at extension
  cases extension with
  | cons scheme head tail =>
    cases tail
    have binders : TypeParameterBindersWellFormed lexical := by
      rw [TypeParameterBindersWellFormed, head.context_fields.2.2.1]
      simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
        Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
    have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
    have narrow : TypeAdmissible lexical (.fixed ⟨false, .w8⟩) := ⟨binders, .builtin (.fixed ⟨false, .w8⟩)⟩
    have read := shape.parts.read.typed scheme shape.binderRequirements word head.local_self
      head.local_scheme_requirements_self
    have converted : ExpressionHasType function.typedBody lexical shape.parts.converted.value.node.id
        (.fixed ⟨false, .w8⟩) := shape.parts.converted.typed rfl narrow read
    let locals := lexical.withLocal shape.parts.target.id shape.parts.target.scheme shape.parts.target.schemeRequirements
    have targetExtended : BinderExtends function.typedBody.owner lexical shape.parts.target locals := by
      apply BinderExtends.intro
      · exact {
          owned := shape.targetOwner
          scheme := shape.targetScheme.symm ▸ SchemeWellFormed.monoAdmissible narrow
          quantified_fresh := by rw [shape.targetScheme]; simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]
          monomorphic_requirements_empty := fun _ => shape.targetRequirements }
      · cases head
        simp [LocalFresh, Context.withLocal, checkedBodyContext, declarationContext,
          Context.ofSignatures, Context.forDeclaration, Context.withAssumptions,
          Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.targetDistinct]
    have localNarrow : TypeAdmissible locals (.fixed ⟨false, .w8⟩) := ⟨binders, .builtin (.fixed ⟨false, .w8⟩)⟩
    have initializedTyped : StatementHasType function.typedBody ⟨.fixed ⟨false, .w8⟩, 0⟩ lexical
        shape.parts.initialized.id locals ordinary := by
      apply StatementHasType.letInitialized (lookupStatement?_sound shape.parts.initializedFound)
        shape.parts.initializedForm
      · simpa only [shape.targetScheme, TypeSystem.Scheme.mono] using converted
      · rw [shape.targetScheme]; rfl
      · rw [shape.targetScheme]; rfl
      · exact targetExtended
      · exact shape.initializedType
    have writable : WritableLocal locals shape.parts.resolution.target.root (.fixed ⟨false, .w8⟩) := by
      rw [shape.targetRoot]
      exact .intro targetExtended.local_self (shape.targetScheme.symm ▸ SchemeWellFormed.monoAdmissible localNarrow)
        (by rw [shape.targetScheme]; rfl) (by rw [shape.targetScheme]; rfl)
    have rightTyped := shape.parts.rightRead.typed shape.targetScheme shape.targetRequirements localNarrow
      targetExtended.local_self targetExtended.local_scheme_requirements_self
    have assignmentTyped : SourceAssignmentHasType function.typedBody locals shape.parts.resolution .add
        shape.parts.rightRead.node.id :=
      .fixedCompound .add (.intro writable (by rw [shape.targetBare]; exact .nil _) shape.targetType) rightTyped
        shape.assignmentRequirements
    have assignedTyped : StatementHasType function.typedBody ⟨.fixed ⟨false, .w8⟩, 0⟩ locals
        shape.parts.assignment.id locals ordinary :=
      .assignValue (lookupStatement?_sound shape.parts.assignmentFound) shape.parts.assignmentForm assignmentTyped
        shape.assignmentType
    have returnedValue := shape.parts.returnRead.typed shape.targetScheme shape.targetRequirements localNarrow
      targetExtended.local_self targetExtended.local_scheme_requirements_self
    exact ⟨_, .cons initializedTyped (.cons assignedTyped (.singleton (.returnValue
      (lookupStatement?_sound shape.parts.returnedFound) shape.parts.returnedForm returnedValue shape.returnedType)))⟩

def observeDoubled (function : CheckedFunction) (signature : ProgramFunctionSignature) :
    IO (DoubledShape function signature) := do
  let parts ← observeDoubledParts function.typedBody
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "doubled parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "doubled inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.fixed ⟨false, .w8⟩]) "doubled returns"
  let ⟨binderScheme⟩ ← observed (parts.binder.scheme = .mono .word) "doubled binderScheme"
  let ⟨binderRequirements⟩ ← observed (parts.binder.schemeRequirements = []) "doubled binderRequirements"
  let ⟨targetScheme⟩ ← observed (parts.target.scheme = .mono (.fixed ⟨false, .w8⟩)) "doubled targetScheme"
  let ⟨targetRequirements⟩ ← observed (parts.target.schemeRequirements = []) "doubled targetRequirements"
  let ⟨targetOwner⟩ ← observed (parts.target.id.owner = function.typedBody.owner) "doubled targetOwner"
  let ⟨targetDistinct⟩ ← observed (parts.target.id ≠ parts.binder.id) "doubled targetDistinct"
  let ⟨targetOrdinary⟩ ← observed (parts.target.comptime = false) "doubled targetOrdinary"
  let ⟨initializedType⟩ ← observed (parts.initialized.type = .unit) "doubled initializedType"
  let ⟨assignmentType⟩ ← observed (parts.assignment.type = .unit) "doubled assignmentType"
  let ⟨returnedType⟩ ← observed (parts.returned.type = .fixed ⟨false, .w8⟩) "doubled returnedType"
  let ⟨targetRoot⟩ ← observed (parts.resolution.target.root = parts.target.id) "doubled targetRoot"
  let ⟨targetType⟩ ← observed (parts.resolution.target.type = .fixed ⟨false, .w8⟩) "doubled targetType"
  let ⟨targetBare⟩ ← observed (parts.resolution.target.projections = []) "doubled targetBare"
  let ⟨assignmentRequirements⟩ ← observed (parts.resolution.requirements = []) "doubled assignmentRequirements"
  return ⟨parts, parameters, inputTypes, returns, binderScheme, binderRequirements, targetScheme, targetRequirements,
    targetOwner, targetDistinct, targetOrdinary, initializedType, assignmentType, returnedType, targetRoot,
    targetType, targetBare, assignmentRequirements⟩

/-- The nodes of `shifted`'s body: the read of its parameter, `uint8(value)` initializing the local
`x`, `x <<= value`, whose amount is a second read of the parameter, and the return of `x`, found by
following the statement graph. -/
structure ShiftedParts (source : TypedSource) where
  binder : TypedBinder
  target : TypedBinder
  read : Tests.SourceCoreNamedBranch.Read source binder .word
  converted : Tests.SourceCoreBuiltinCalls.BuiltinCall source (.fixedFromWord ⟨false, .w8⟩) read.node.id
  amountRead : Tests.SourceCoreNamedBranch.Read source binder .word
  returnRead : Tests.SourceCoreNamedBranch.Read source target (.fixed ⟨false, .w8⟩)
  initialized : StatementNode
  assignment : StatementNode
  resolution : AssignmentResolution
  returned : StatementNode
  inputs : source.inputs = [binder]
  roots : source.roots = [.statement initialized.id, .statement assignment.id, .statement returned.id]
  initializedFound : source.lookupStatement? initialized.id = some initialized
  initializedForm : initialized.form = .letDecl target (some converted.value.node.id)
  assignmentFound : source.lookupStatement? assignment.id = some assignment
  assignmentForm : assignment.form = .assignValue resolution .shiftLeft amountRead.node.id
  returnedFound : source.lookupStatement? returned.id = some returned
  returnedForm : returned.form = .returnStmt (some returnRead.node.id)

def observeShiftedParts (source : TypedSource) : IO (ShiftedParts source) := do
  let [binder] := source.inputs | throw (IO.userError "shifted input")
  let [.statement initializedId, .statement assignmentId, .statement returnedId] := source.roots
    | throw (IO.userError "shifted roots")
  let some initialized := source.lookupStatement? initializedId | throw (IO.userError "shifted let")
  let some assignment := source.lookupStatement? assignmentId | throw (IO.userError "shifted assignment")
  let some returned := source.lookupStatement? returnedId | throw (IO.userError "shifted return")
  let .letDecl target (some valueId) := initialized.form | throw (IO.userError "shifted let form")
  let .assignValue resolution .shiftLeft rightId := assignment.form | throw (IO.userError "shifted assignment form")
  let .returnStmt (some returnId) := returned.form | throw (IO.userError "shifted return form")
  let some valueNode := source.lookupExpression? valueId | throw (IO.userError "shifted conversion node")
  let .call calleeId [readId] _ := valueNode.form | throw (IO.userError "shifted conversion form")
  let some calleeNode := source.lookupExpression? calleeId | throw (IO.userError "shifted callee")
  let some readNode := source.lookupExpression? readId | throw (IO.userError "shifted read")
  let some rightNode := source.lookupExpression? rightId | throw (IO.userError "shifted right read")
  let some returnNode := source.lookupExpression? returnId | throw (IO.userError "shifted returned read")
  let read ← Tests.SourceCoreNamedBranch.observeRead source binder readNode .word
  let converted ← observeConversion source (.fixedFromWord ⟨false, .w8⟩) read.node.id calleeNode valueNode
  let amountRead ← Tests.SourceCoreNamedBranch.observeRead source binder rightNode .word
  let returnRead ← Tests.SourceCoreNamedBranch.observeRead source target returnNode (.fixed ⟨false, .w8⟩)
  let ⟨inputs⟩ ← observed (source.inputs = [binder]) "shifted inputs"
  let ⟨roots⟩ ← observed (source.roots = [.statement initialized.id, .statement assignment.id, .statement returned.id])
    "shifted roots shape"
  let ⟨initializedFound⟩ ← observed (source.lookupStatement? initialized.id = some initialized) "shifted initializedFound"
  let ⟨initializedForm⟩ ← observed (initialized.form = .letDecl target (some converted.value.node.id))
    "shifted initializedForm"
  let ⟨assignmentFound⟩ ← observed (source.lookupStatement? assignment.id = some assignment) "shifted assignmentFound"
  let ⟨assignmentForm⟩ ← observed (assignment.form = .assignValue resolution .shiftLeft amountRead.node.id)
    "shifted assignmentForm"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "shifted returnedFound"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some returnRead.node.id)) "shifted returnedForm"
  return ⟨binder, target, read, converted, amountRead, returnRead, initialized, assignment, resolution, returned,
    inputs, roots, initializedFound, initializedForm, assignmentFound, assignmentForm, returnedFound, returnedForm⟩

/-- `shifted`'s body: `let x: uint8 = uint8(value)`, `x <<= value` at the fixed-width local, whose
amount keeps its own type, `Word`, and the return of `x`. -/
structure ShiftedShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  parts : ShiftedParts function.typedBody
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [.fixed ⟨false, .w8⟩]
  binderScheme : parts.binder.scheme = .mono .word
  binderRequirements : parts.binder.schemeRequirements = []
  targetScheme : parts.target.scheme = .mono (.fixed ⟨false, .w8⟩)
  targetRequirements : parts.target.schemeRequirements = []
  targetOwner : parts.target.id.owner = function.typedBody.owner
  targetDistinct : parts.target.id ≠ parts.binder.id
  targetOrdinary : parts.target.comptime = false
  initializedType : parts.initialized.type = .unit
  assignmentType : parts.assignment.type = .unit
  returnedType : parts.returned.type = .fixed ⟨false, .w8⟩
  targetRoot : parts.resolution.target.root = parts.target.id
  targetType : parts.resolution.target.type = .fixed ⟨false, .w8⟩
  targetBare : parts.resolution.target.projections = []
  assignmentRequirements : parts.resolution.requirements = []

theorem ShiftedShape.statementTyping {function : CheckedFunction} {signature : ProgramFunctionSignature}
    (shape : ShiftedShape function signature) (signatures : ProgramSignatures) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.parts.initialized.id, shape.parts.assignment.id, shape.parts.returned.id] :=
    statementRoots_injective (roots.symm.trans shape.parts.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts :=
    {type := .fixed ⟨false, .w8⟩, hasValue := true, sawReturn := true, control := .returned}
  let ordinary : StatementFacts := {type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit}
  refine ⟨BodyFacts.cons ordinary (BodyFacts.cons ordinary (BodyFacts.singleton facts)), rfl, ?_⟩
  intro lexical extension
  rw [shape.parts.inputs, shape.inputTypes] at extension
  cases extension with
  | cons scheme head tail =>
    cases tail
    have binders : TypeParameterBindersWellFormed lexical := by
      rw [TypeParameterBindersWellFormed, head.context_fields.2.2.1]
      simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
        Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
    have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
    have narrow : TypeAdmissible lexical (.fixed ⟨false, .w8⟩) := ⟨binders, .builtin (.fixed ⟨false, .w8⟩)⟩
    have read := shape.parts.read.typed scheme shape.binderRequirements word head.local_self
      head.local_scheme_requirements_self
    have converted : ExpressionHasType function.typedBody lexical shape.parts.converted.value.node.id
        (.fixed ⟨false, .w8⟩) := shape.parts.converted.typed rfl narrow read
    let locals := lexical.withLocal shape.parts.target.id shape.parts.target.scheme shape.parts.target.schemeRequirements
    have targetExtended : BinderExtends function.typedBody.owner lexical shape.parts.target locals := by
      apply BinderExtends.intro
      · exact {
          owned := shape.targetOwner
          scheme := shape.targetScheme.symm ▸ SchemeWellFormed.monoAdmissible narrow
          quantified_fresh := by rw [shape.targetScheme]; simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]
          monomorphic_requirements_empty := fun _ => shape.targetRequirements }
      · cases head
        simp [LocalFresh, Context.withLocal, checkedBodyContext, declarationContext,
          Context.ofSignatures, Context.forDeclaration, Context.withAssumptions,
          Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.targetDistinct]
    have localNarrow : TypeAdmissible locals (.fixed ⟨false, .w8⟩) := ⟨binders, .builtin (.fixed ⟨false, .w8⟩)⟩
    have initializedTyped : StatementHasType function.typedBody ⟨.fixed ⟨false, .w8⟩, 0⟩ lexical
        shape.parts.initialized.id locals ordinary := by
      apply StatementHasType.letInitialized (lookupStatement?_sound shape.parts.initializedFound)
        shape.parts.initializedForm
      · simpa only [shape.targetScheme, TypeSystem.Scheme.mono] using converted
      · rw [shape.targetScheme]; rfl
      · rw [shape.targetScheme]; rfl
      · exact targetExtended
      · exact shape.initializedType
    have writable : WritableLocal locals shape.parts.resolution.target.root (.fixed ⟨false, .w8⟩) := by
      rw [shape.targetRoot]
      exact .intro targetExtended.local_self (shape.targetScheme.symm ▸ SchemeWellFormed.monoAdmissible localNarrow)
        (by rw [shape.targetScheme]; rfl) (by rw [shape.targetScheme]; rfl)
    have localWord : TypeAdmissible locals .word := ⟨binders, .builtin .word⟩
    have amountTyped := shape.parts.amountRead.typed scheme shape.binderRequirements localWord
      (.tail shape.targetDistinct head.local_self) (.tail shape.targetDistinct head.local_scheme_requirements_self)
    have assignmentTyped : SourceAssignmentHasType function.typedBody locals shape.parts.resolution .shiftLeft
        shape.parts.amountRead.node.id :=
      .shiftCompound .shiftLeft (.intro writable (by rw [shape.targetBare]; exact .nil _) shape.targetType)
        (.fixed ⟨false, .w8⟩) amountTyped .word shape.assignmentRequirements
    have assignedTyped : StatementHasType function.typedBody ⟨.fixed ⟨false, .w8⟩, 0⟩ locals
        shape.parts.assignment.id locals ordinary :=
      .assignValue (lookupStatement?_sound shape.parts.assignmentFound) shape.parts.assignmentForm assignmentTyped
        shape.assignmentType
    have returnedValue := shape.parts.returnRead.typed shape.targetScheme shape.targetRequirements localNarrow
      targetExtended.local_self targetExtended.local_scheme_requirements_self
    exact ⟨_, .cons initializedTyped (.cons assignedTyped (.singleton (.returnValue
      (lookupStatement?_sound shape.parts.returnedFound) shape.parts.returnedForm returnedValue shape.returnedType)))⟩

def observeShifted (function : CheckedFunction) (signature : ProgramFunctionSignature) :
    IO (ShiftedShape function signature) := do
  let parts ← observeShiftedParts function.typedBody
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "shifted parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "shifted inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.fixed ⟨false, .w8⟩]) "shifted returns"
  let ⟨binderScheme⟩ ← observed (parts.binder.scheme = .mono .word) "shifted binderScheme"
  let ⟨binderRequirements⟩ ← observed (parts.binder.schemeRequirements = []) "shifted binderRequirements"
  let ⟨targetScheme⟩ ← observed (parts.target.scheme = .mono (.fixed ⟨false, .w8⟩)) "shifted targetScheme"
  let ⟨targetRequirements⟩ ← observed (parts.target.schemeRequirements = []) "shifted targetRequirements"
  let ⟨targetOwner⟩ ← observed (parts.target.id.owner = function.typedBody.owner) "shifted targetOwner"
  let ⟨targetDistinct⟩ ← observed (parts.target.id ≠ parts.binder.id) "shifted targetDistinct"
  let ⟨targetOrdinary⟩ ← observed (parts.target.comptime = false) "shifted targetOrdinary"
  let ⟨initializedType⟩ ← observed (parts.initialized.type = .unit) "shifted initializedType"
  let ⟨assignmentType⟩ ← observed (parts.assignment.type = .unit) "shifted assignmentType"
  let ⟨returnedType⟩ ← observed (parts.returned.type = .fixed ⟨false, .w8⟩) "shifted returnedType"
  let ⟨targetRoot⟩ ← observed (parts.resolution.target.root = parts.target.id) "shifted targetRoot"
  let ⟨targetType⟩ ← observed (parts.resolution.target.type = .fixed ⟨false, .w8⟩) "shifted targetType"
  let ⟨targetBare⟩ ← observed (parts.resolution.target.projections = []) "shifted targetBare"
  let ⟨assignmentRequirements⟩ ← observed (parts.resolution.requirements = []) "shifted assignmentRequirements"
  return ⟨parts, parameters, inputTypes, returns, binderScheme, binderRequirements, targetScheme, targetRequirements,
    targetOwner, targetDistinct, targetOrdinary, initializedType, assignmentType, returnedType, targetRoot,
    targetType, targetBare, assignmentRequirements⟩

/-- The nodes of `flipped`'s body: the read of its parameter, `uint8(value)` initializing the local
`x`, `x ~=` and the return of `x`, found by following the statement graph. -/
structure FlippedParts (source : TypedSource) where
  binder : TypedBinder
  target : TypedBinder
  read : Tests.SourceCoreNamedBranch.Read source binder .word
  converted : Tests.SourceCoreBuiltinCalls.BuiltinCall source (.fixedFromWord ⟨false, .w8⟩) read.node.id
  returnRead : Tests.SourceCoreNamedBranch.Read source target (.fixed ⟨false, .w8⟩)
  initialized : StatementNode
  assignment : StatementNode
  resolution : AssignmentResolution
  returned : StatementNode
  inputs : source.inputs = [binder]
  roots : source.roots = [.statement initialized.id, .statement assignment.id, .statement returned.id]
  initializedFound : source.lookupStatement? initialized.id = some initialized
  initializedForm : initialized.form = .letDecl target (some converted.value.node.id)
  assignmentFound : source.lookupStatement? assignment.id = some assignment
  assignmentForm : assignment.form = .assignBitNot resolution
  returnedFound : source.lookupStatement? returned.id = some returned
  returnedForm : returned.form = .returnStmt (some returnRead.node.id)

def observeFlippedParts (source : TypedSource) : IO (FlippedParts source) := do
  let [binder] := source.inputs | throw (IO.userError "flipped input")
  let [.statement initializedId, .statement assignmentId, .statement returnedId] := source.roots
    | throw (IO.userError "flipped roots")
  let some initialized := source.lookupStatement? initializedId | throw (IO.userError "flipped let")
  let some assignment := source.lookupStatement? assignmentId | throw (IO.userError "flipped assignment")
  let some returned := source.lookupStatement? returnedId | throw (IO.userError "flipped return")
  let .letDecl target (some valueId) := initialized.form | throw (IO.userError "flipped let form")
  let .assignBitNot resolution := assignment.form | throw (IO.userError "flipped assignment form")
  let .returnStmt (some returnId) := returned.form | throw (IO.userError "flipped return form")
  let some valueNode := source.lookupExpression? valueId | throw (IO.userError "flipped conversion node")
  let .call calleeId [readId] _ := valueNode.form | throw (IO.userError "flipped conversion form")
  let some calleeNode := source.lookupExpression? calleeId | throw (IO.userError "flipped callee")
  let some readNode := source.lookupExpression? readId | throw (IO.userError "flipped read")
  let some returnNode := source.lookupExpression? returnId | throw (IO.userError "flipped returned read")
  let read ← Tests.SourceCoreNamedBranch.observeRead source binder readNode .word
  let converted ← observeConversion source (.fixedFromWord ⟨false, .w8⟩) read.node.id calleeNode valueNode
  let returnRead ← Tests.SourceCoreNamedBranch.observeRead source target returnNode (.fixed ⟨false, .w8⟩)
  let ⟨inputs⟩ ← observed (source.inputs = [binder]) "flipped inputs"
  let ⟨roots⟩ ← observed (source.roots = [.statement initialized.id, .statement assignment.id, .statement returned.id])
    "flipped roots shape"
  let ⟨initializedFound⟩ ← observed (source.lookupStatement? initialized.id = some initialized) "flipped initializedFound"
  let ⟨initializedForm⟩ ← observed (initialized.form = .letDecl target (some converted.value.node.id))
    "flipped initializedForm"
  let ⟨assignmentFound⟩ ← observed (source.lookupStatement? assignment.id = some assignment) "flipped assignmentFound"
  let ⟨assignmentForm⟩ ← observed (assignment.form = .assignBitNot resolution) "flipped assignmentForm"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "flipped returnedFound"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some returnRead.node.id)) "flipped returnedForm"
  return ⟨binder, target, read, converted, returnRead, initialized, assignment, resolution, returned,
    inputs, roots, initializedFound, initializedForm, assignmentFound, assignmentForm, returnedFound, returnedForm⟩

/-- `flipped`'s body: `let x: uint8 = uint8(value)`, `x ~=` at the fixed-width local, and the return
of `x`. -/
structure FlippedShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  parts : FlippedParts function.typedBody
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [.fixed ⟨false, .w8⟩]
  binderScheme : parts.binder.scheme = .mono .word
  binderRequirements : parts.binder.schemeRequirements = []
  targetScheme : parts.target.scheme = .mono (.fixed ⟨false, .w8⟩)
  targetRequirements : parts.target.schemeRequirements = []
  targetOwner : parts.target.id.owner = function.typedBody.owner
  targetDistinct : parts.target.id ≠ parts.binder.id
  targetOrdinary : parts.target.comptime = false
  initializedType : parts.initialized.type = .unit
  assignmentType : parts.assignment.type = .unit
  returnedType : parts.returned.type = .fixed ⟨false, .w8⟩
  targetRoot : parts.resolution.target.root = parts.target.id
  targetType : parts.resolution.target.type = .fixed ⟨false, .w8⟩
  targetBare : parts.resolution.target.projections = []
  assignmentRequirements : parts.resolution.requirements = []

theorem FlippedShape.statementTyping {function : CheckedFunction} {signature : ProgramFunctionSignature}
    (shape : FlippedShape function signature) (signatures : ProgramSignatures) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.parts.initialized.id, shape.parts.assignment.id, shape.parts.returned.id] :=
    statementRoots_injective (roots.symm.trans shape.parts.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts :=
    {type := .fixed ⟨false, .w8⟩, hasValue := true, sawReturn := true, control := .returned}
  let ordinary : StatementFacts := {type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit}
  refine ⟨BodyFacts.cons ordinary (BodyFacts.cons ordinary (BodyFacts.singleton facts)), rfl, ?_⟩
  intro lexical extension
  rw [shape.parts.inputs, shape.inputTypes] at extension
  cases extension with
  | cons scheme head tail =>
    cases tail
    have binders : TypeParameterBindersWellFormed lexical := by
      rw [TypeParameterBindersWellFormed, head.context_fields.2.2.1]
      simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
        Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
    have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
    have narrow : TypeAdmissible lexical (.fixed ⟨false, .w8⟩) := ⟨binders, .builtin (.fixed ⟨false, .w8⟩)⟩
    have read := shape.parts.read.typed scheme shape.binderRequirements word head.local_self
      head.local_scheme_requirements_self
    have converted : ExpressionHasType function.typedBody lexical shape.parts.converted.value.node.id
        (.fixed ⟨false, .w8⟩) := shape.parts.converted.typed rfl narrow read
    let locals := lexical.withLocal shape.parts.target.id shape.parts.target.scheme shape.parts.target.schemeRequirements
    have targetExtended : BinderExtends function.typedBody.owner lexical shape.parts.target locals := by
      apply BinderExtends.intro
      · exact {
          owned := shape.targetOwner
          scheme := shape.targetScheme.symm ▸ SchemeWellFormed.monoAdmissible narrow
          quantified_fresh := by rw [shape.targetScheme]; simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]
          monomorphic_requirements_empty := fun _ => shape.targetRequirements }
      · cases head
        simp [LocalFresh, Context.withLocal, checkedBodyContext, declarationContext,
          Context.ofSignatures, Context.forDeclaration, Context.withAssumptions,
          Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.targetDistinct]
    have localNarrow : TypeAdmissible locals (.fixed ⟨false, .w8⟩) := ⟨binders, .builtin (.fixed ⟨false, .w8⟩)⟩
    have initializedTyped : StatementHasType function.typedBody ⟨.fixed ⟨false, .w8⟩, 0⟩ lexical
        shape.parts.initialized.id locals ordinary := by
      apply StatementHasType.letInitialized (lookupStatement?_sound shape.parts.initializedFound)
        shape.parts.initializedForm
      · simpa only [shape.targetScheme, TypeSystem.Scheme.mono] using converted
      · rw [shape.targetScheme]; rfl
      · rw [shape.targetScheme]; rfl
      · exact targetExtended
      · exact shape.initializedType
    have writable : WritableLocal locals shape.parts.resolution.target.root (.fixed ⟨false, .w8⟩) := by
      rw [shape.targetRoot]
      exact .intro targetExtended.local_self (shape.targetScheme.symm ▸ SchemeWellFormed.monoAdmissible localNarrow)
        (by rw [shape.targetScheme]; rfl) (by rw [shape.targetScheme]; rfl)
    have assignmentTyped : SourceBitNotAssignmentValid function.typedBody locals shape.parts.resolution :=
      .intro (.intro writable (by rw [shape.targetBare]; exact .nil _) shape.targetType) (.fixed ⟨false, .w8⟩)
        shape.assignmentRequirements
    have assignedTyped : StatementHasType function.typedBody ⟨.fixed ⟨false, .w8⟩, 0⟩ locals
        shape.parts.assignment.id locals ordinary :=
      .assignBitNot (lookupStatement?_sound shape.parts.assignmentFound) shape.parts.assignmentForm assignmentTyped
        shape.assignmentType
    have returnedValue := shape.parts.returnRead.typed shape.targetScheme shape.targetRequirements localNarrow
      targetExtended.local_self targetExtended.local_scheme_requirements_self
    exact ⟨_, .cons initializedTyped (.cons assignedTyped (.singleton (.returnValue
      (lookupStatement?_sound shape.parts.returnedFound) shape.parts.returnedForm returnedValue shape.returnedType)))⟩

def observeFlipped (function : CheckedFunction) (signature : ProgramFunctionSignature) :
    IO (FlippedShape function signature) := do
  let parts ← observeFlippedParts function.typedBody
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "flipped parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "flipped inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.fixed ⟨false, .w8⟩]) "flipped returns"
  let ⟨binderScheme⟩ ← observed (parts.binder.scheme = .mono .word) "flipped binderScheme"
  let ⟨binderRequirements⟩ ← observed (parts.binder.schemeRequirements = []) "flipped binderRequirements"
  let ⟨targetScheme⟩ ← observed (parts.target.scheme = .mono (.fixed ⟨false, .w8⟩)) "flipped targetScheme"
  let ⟨targetRequirements⟩ ← observed (parts.target.schemeRequirements = []) "flipped targetRequirements"
  let ⟨targetOwner⟩ ← observed (parts.target.id.owner = function.typedBody.owner) "flipped targetOwner"
  let ⟨targetDistinct⟩ ← observed (parts.target.id ≠ parts.binder.id) "flipped targetDistinct"
  let ⟨targetOrdinary⟩ ← observed (parts.target.comptime = false) "flipped targetOrdinary"
  let ⟨initializedType⟩ ← observed (parts.initialized.type = .unit) "flipped initializedType"
  let ⟨assignmentType⟩ ← observed (parts.assignment.type = .unit) "flipped assignmentType"
  let ⟨returnedType⟩ ← observed (parts.returned.type = .fixed ⟨false, .w8⟩) "flipped returnedType"
  let ⟨targetRoot⟩ ← observed (parts.resolution.target.root = parts.target.id) "flipped targetRoot"
  let ⟨targetType⟩ ← observed (parts.resolution.target.type = .fixed ⟨false, .w8⟩) "flipped targetType"
  let ⟨targetBare⟩ ← observed (parts.resolution.target.projections = []) "flipped targetBare"
  let ⟨assignmentRequirements⟩ ← observed (parts.resolution.requirements = []) "flipped assignmentRequirements"
  return ⟨parts, parameters, inputTypes, returns, binderScheme, binderRequirements, targetScheme, targetRequirements,
    targetOwner, targetDistinct, targetOrdinary, initializedType, assignmentType, returnedType, targetRoot,
    targetType, targetBare, assignmentRequirements⟩

/-- The nodes of `stored`'s body: the declaration of its local mapping `table`, `table[value] = value`,
whose key and right side read the parameter, and the return of `table[value]`, the index of a read of
`table` by a third read of the parameter, found by following the statement graph. -/
structure StoredParts (source : TypedSource) where
  binder : TypedBinder
  table : TypedBinder
  keyRead : Tests.SourceCoreNamedBranch.Read source binder .word
  rightRead : Tests.SourceCoreNamedBranch.Read source binder .word
  baseRead : Tests.SourceCoreNamedBranch.Read source table (.mapping .word .word)
  indexKey : Tests.SourceCoreNamedBranch.Read source binder .word
  index : ExpressionNode
  declared : StatementNode
  assignment : StatementNode
  resolution : AssignmentResolution
  returned : StatementNode
  inputs : source.inputs = [binder]
  roots : source.roots = [.statement declared.id, .statement assignment.id, .statement returned.id]
  declaredFound : source.lookupStatement? declared.id = some declared
  declaredForm : declared.form = .letDecl table none
  assignmentFound : source.lookupStatement? assignment.id = some assignment
  assignmentForm : assignment.form = .assignValue resolution .equal rightRead.node.id
  targetRoot : resolution.target.root = table.id
  targetProjections : resolution.target.projections = [.index keyRead.node.id]
  targetType : resolution.target.type = .word
  indexFound : source.lookupExpression? index.id = some index
  indexForm : index.form = .index baseRead.node.id indexKey.node.id
  indexRaw : index.rawType = .word
  indexType : index.type = .word
  indexRequirements : index.requirements = []
  indexCoercions : index.coercions = []
  returnedFound : source.lookupStatement? returned.id = some returned
  returnedForm : returned.form = .returnStmt (some index.id)

def observeStoredParts (source : TypedSource) : IO (StoredParts source) := do
  let [binder] := source.inputs | throw (IO.userError "stored input")
  let [.statement declaredId, .statement assignmentId, .statement returnedId] := source.roots
    | throw (IO.userError "stored roots")
  let some declared := source.lookupStatement? declaredId | throw (IO.userError "stored let")
  let some assignment := source.lookupStatement? assignmentId | throw (IO.userError "stored assignment")
  let some returned := source.lookupStatement? returnedId | throw (IO.userError "stored return")
  let .letDecl table none := declared.form | throw (IO.userError "stored let form")
  let .assignValue resolution .equal rightId := assignment.form | throw (IO.userError "stored assignment form")
  let [.index keyId] := resolution.target.projections | throw (IO.userError "stored target projections")
  let .returnStmt (some indexId) := returned.form | throw (IO.userError "stored return form")
  let some keyNode := source.lookupExpression? keyId | throw (IO.userError "stored key")
  let some rightNode := source.lookupExpression? rightId | throw (IO.userError "stored right side")
  let some index := source.lookupExpression? indexId | throw (IO.userError "stored index")
  let .index baseId indexKeyId := index.form | throw (IO.userError "stored index form")
  let some baseNode := source.lookupExpression? baseId | throw (IO.userError "stored base")
  let some indexKeyNode := source.lookupExpression? indexKeyId | throw (IO.userError "stored index key")
  let keyRead ← Tests.SourceCoreNamedBranch.observeRead source binder keyNode .word
  let rightRead ← Tests.SourceCoreNamedBranch.observeRead source binder rightNode .word
  let baseRead ← Tests.SourceCoreNamedBranch.observeRead source table baseNode (.mapping .word .word)
  let indexKey ← Tests.SourceCoreNamedBranch.observeRead source binder indexKeyNode .word
  let ⟨inputs⟩ ← observed (source.inputs = [binder]) "stored inputs"
  let ⟨roots⟩ ← observed (source.roots = [.statement declared.id, .statement assignment.id, .statement returned.id])
    "stored roots shape"
  let ⟨declaredFound⟩ ← observed (source.lookupStatement? declared.id = some declared) "stored declaredFound"
  let ⟨declaredForm⟩ ← observed (declared.form = .letDecl table none) "stored declaredForm"
  let ⟨assignmentFound⟩ ← observed (source.lookupStatement? assignment.id = some assignment) "stored assignmentFound"
  let ⟨assignmentForm⟩ ← observed (assignment.form = .assignValue resolution .equal rightRead.node.id)
    "stored assignmentForm"
  let ⟨targetRoot⟩ ← observed (resolution.target.root = table.id) "stored targetRoot"
  let ⟨targetProjections⟩ ← observed (resolution.target.projections = [.index keyRead.node.id])
    "stored targetProjections"
  let ⟨targetType⟩ ← observed (resolution.target.type = .word) "stored targetType"
  let ⟨indexFound⟩ ← observed (source.lookupExpression? index.id = some index) "stored indexFound"
  let ⟨indexForm⟩ ← observed (index.form = .index baseRead.node.id indexKey.node.id) "stored indexForm"
  let ⟨indexRaw⟩ ← observed (index.rawType = .word) "stored indexRaw"
  let ⟨indexType⟩ ← observed (index.type = .word) "stored indexType"
  let ⟨indexRequirements⟩ ← observed (index.requirements = []) "stored indexRequirements"
  let ⟨indexCoercions⟩ ← observed (index.coercions = []) "stored indexCoercions"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "stored returnedFound"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some index.id)) "stored returnedForm"
  return ⟨binder, table, keyRead, rightRead, baseRead, indexKey, index, declared, assignment, resolution, returned,
    inputs, roots, declaredFound, declaredForm, assignmentFound, assignmentForm, targetRoot, targetProjections,
    targetType, indexFound, indexForm, indexRaw, indexType, indexRequirements, indexCoercions, returnedFound,
    returnedForm⟩

/-- `stored`'s body: `let table: mapping(Word => Word)`, `table[value] = value` through the local's
index and the return of `table[value]`. -/
structure StoredShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  parts : StoredParts function.typedBody
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [.word]
  binderScheme : parts.binder.scheme = .mono .word
  binderRequirements : parts.binder.schemeRequirements = []
  tableScheme : parts.table.scheme = .mono (.mapping .word .word)
  tableRequirements : parts.table.schemeRequirements = []
  tableOwner : parts.table.id.owner = function.typedBody.owner
  tableDistinct : parts.table.id ≠ parts.binder.id
  declaredType : parts.declared.type = .unit
  assignmentType : parts.assignment.type = .unit
  returnedType : parts.returned.type = .word
  assignmentRequirements : parts.resolution.requirements = []

theorem StoredShape.statementTyping {function : CheckedFunction} {signature : ProgramFunctionSignature}
    (shape : StoredShape function signature) (signatures : ProgramSignatures) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.parts.declared.id, shape.parts.assignment.id, shape.parts.returned.id] :=
    statementRoots_injective (roots.symm.trans shape.parts.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type := .word, hasValue := true, sawReturn := true, control := .returned}
  let ordinary : StatementFacts := {type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit}
  refine ⟨BodyFacts.cons ordinary (BodyFacts.cons ordinary (BodyFacts.singleton facts)), rfl, ?_⟩
  intro lexical extension
  rw [shape.parts.inputs, shape.inputTypes] at extension
  cases extension with
  | cons scheme head tail =>
    cases tail
    have binders : TypeParameterBindersWellFormed lexical := by
      rw [TypeParameterBindersWellFormed, head.context_fields.2.2.1]
      simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
        Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
    have mapping : TypeAdmissible lexical (.mapping .word .word) :=
      ⟨binders, .mapping (.builtin .word) (.builtin .word)⟩
    let locals := lexical.withLocal shape.parts.table.id shape.parts.table.scheme shape.parts.table.schemeRequirements
    have tableExtended : BinderExtends function.typedBody.owner lexical shape.parts.table locals := by
      apply BinderExtends.intro
      · exact {
          owned := shape.tableOwner
          scheme := shape.tableScheme.symm ▸ SchemeWellFormed.monoAdmissible mapping
          quantified_fresh := by rw [shape.tableScheme]; simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]
          monomorphic_requirements_empty := fun _ => shape.tableRequirements }
      · cases head
        simp [LocalFresh, Context.withLocal, checkedBodyContext, declarationContext,
          Context.ofSignatures, Context.forDeclaration, Context.withAssumptions,
          Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.tableDistinct]
    have localWord : TypeAdmissible locals .word := ⟨binders, .builtin .word⟩
    have localMapping : TypeAdmissible locals (.mapping .word .word) :=
      ⟨binders, .mapping (.builtin .word) (.builtin .word)⟩
    have declaredTyped : StatementHasType function.typedBody ⟨.word, 0⟩ lexical shape.parts.declared.id locals
        ordinary := by
      apply StatementHasType.letUninitialized (lookupStatement?_sound shape.parts.declaredFound)
        shape.parts.declaredForm
      · rw [shape.tableScheme]; rfl
      · rw [shape.tableScheme]; rfl
      · exact tableExtended
      · exact shape.declaredType
    have parameterLookup : locals.LocalLookup shape.parts.binder.id shape.parts.binder.scheme :=
      .tail shape.tableDistinct head.local_self
    have parameterRequirements :
        locals.LocalSchemeRequirementsLookup shape.parts.binder.id shape.parts.binder.schemeRequirements :=
      .tail shape.tableDistinct head.local_scheme_requirements_self
    have keyTyped := shape.parts.keyRead.typed scheme shape.binderRequirements localWord parameterLookup
      parameterRequirements
    have rightTyped := shape.parts.rightRead.typed scheme shape.binderRequirements localWord parameterLookup
      parameterRequirements
    have writable : WritableLocal locals shape.parts.resolution.target.root (.mapping .word .word) := by
      rw [shape.parts.targetRoot]
      exact .intro tableExtended.local_self (shape.tableScheme.symm ▸ SchemeWellFormed.monoAdmissible localMapping)
        (by rw [shape.tableScheme]; rfl) (by rw [shape.tableScheme]; rfl)
    have assignmentTyped : SourceAssignmentHasType function.typedBody locals shape.parts.resolution .equal
        shape.parts.rightRead.node.id :=
      .equal (.intro writable (by rw [shape.parts.targetProjections]; exact .index keyTyped (.nil _))
        shape.parts.targetType) rightTyped shape.assignmentRequirements
    have assignedTyped : StatementHasType function.typedBody ⟨.word, 0⟩ locals shape.parts.assignment.id locals
        ordinary :=
      .assignValue (lookupStatement?_sound shape.parts.assignmentFound) shape.parts.assignmentForm assignmentTyped
        shape.assignmentType
    have baseTyped := shape.parts.baseRead.typed shape.tableScheme shape.tableRequirements localMapping
      tableExtended.local_self tableExtended.local_scheme_requirements_self
    have indexKeyTyped := shape.parts.indexKey.typed scheme shape.binderRequirements localWord parameterLookup
      parameterRequirements
    have indexTyped : ExpressionHasType function.typedBody locals shape.parts.index.id shape.parts.index.type := by
      refine .intro (lookupExpression?_sound shape.parts.indexFound)
        (shape.parts.indexForm ▸ ExpressionFormHasRawType.index baseTyped indexKeyTyped) shape.parts.indexRaw
        localWord (Eq.mp (congrArg (TypeAdmissible locals) shape.parts.indexType.symm) localWord) ?_
      rw [shape.parts.indexRequirements, shape.parts.indexCoercions, shape.parts.indexType]
      exact .ordinary (by intro id member; cases member) (.nil _) rfl
    rw [shape.parts.indexType] at indexTyped
    exact ⟨_, .cons declaredTyped (.cons assignedTyped (.singleton (.returnValue
      (lookupStatement?_sound shape.parts.returnedFound) shape.parts.returnedForm indexTyped shape.returnedType)))⟩

def observeStored (function : CheckedFunction) (signature : ProgramFunctionSignature) :
    IO (StoredShape function signature) := do
  let parts ← observeStoredParts function.typedBody
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "stored parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "stored inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.word]) "stored returns"
  let ⟨binderScheme⟩ ← observed (parts.binder.scheme = .mono .word) "stored binderScheme"
  let ⟨binderRequirements⟩ ← observed (parts.binder.schemeRequirements = []) "stored binderRequirements"
  let ⟨tableScheme⟩ ← observed (parts.table.scheme = .mono (.mapping .word .word)) "stored tableScheme"
  let ⟨tableRequirements⟩ ← observed (parts.table.schemeRequirements = []) "stored tableRequirements"
  let ⟨tableOwner⟩ ← observed (parts.table.id.owner = function.typedBody.owner) "stored tableOwner"
  let ⟨tableDistinct⟩ ← observed (parts.table.id ≠ parts.binder.id) "stored tableDistinct"
  let ⟨declaredType⟩ ← observed (parts.declared.type = .unit) "stored declaredType"
  let ⟨assignmentType⟩ ← observed (parts.assignment.type = .unit) "stored assignmentType"
  let ⟨returnedType⟩ ← observed (parts.returned.type = .word) "stored returnedType"
  let ⟨assignmentRequirements⟩ ← observed (parts.resolution.requirements = []) "stored assignmentRequirements"
  return ⟨parts, parameters, inputTypes, returns, binderScheme, binderRequirements, tableScheme, tableRequirements,
    tableOwner, tableDistinct, declaredType, assignmentType, returnedType, assignmentRequirements⟩

/-- The nodes of `summed`'s body: two reads of its parameter, the call of the
builtin closure `wordToInteger` at each, the call of `integerAdd` at both and
the return of the sum, found by following the return statement's expression
graph. -/
structure SummedParts (source : TypedSource) where
  binder : TypedBinder
  leftRead : Tests.SourceCoreNamedBranch.Read source binder .word
  rightRead : Tests.SourceCoreNamedBranch.Read source binder .word
  left : Tests.SourceCoreBuiltinCalls.BuiltinCall source .wordToInteger leftRead.node.id
  right : Tests.SourceCoreBuiltinCalls.BuiltinCall source .wordToInteger rightRead.node.id
  sumCallee : Tests.SourceCoreOperatorCalls.TypedNode source BuiltinFunctionId.integerAdd.type
  sum : Tests.SourceCoreOperatorCalls.TypedNode source .integer
  sumName : String
  sumCalleeForm : sumCallee.node.form = .reference sumName (.builtinFunction .integerAdd)
  sumForm : sum.node.form = .call sumCallee.node.id [left.value.node.id, right.value.node.id]
    (.builtinFunction .integerAdd)
  statement : StatementNode
  inputs : source.inputs = [binder]
  roots : source.roots = [.statement statement.id]
  statementFound : source.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some sum.node.id)

def observeSummedParts (source : TypedSource) : IO (SummedParts source) := do
  let [binder] := source.inputs | throw (IO.userError "summed input")
  let [.statement statementId] := source.roots | throw (IO.userError "summed roots")
  let some statement := source.lookupStatement? statementId | throw (IO.userError "summed statement")
  let .returnStmt (some sumId) := statement.form | throw (IO.userError "summed return")
  let some sumNode := source.lookupExpression? sumId | throw (IO.userError "summed sum node")
  let .call sumCalleeId [leftId, rightId] _ := sumNode.form | throw (IO.userError "summed sum form")
  let some sumCalleeNode := source.lookupExpression? sumCalleeId | throw (IO.userError "summed sum callee")
  let some leftNode := source.lookupExpression? leftId | throw (IO.userError "summed left call")
  let some rightNode := source.lookupExpression? rightId | throw (IO.userError "summed right call")
  let .call leftCalleeId [leftReadId] _ := leftNode.form | throw (IO.userError "summed left form")
  let .call rightCalleeId [rightReadId] _ := rightNode.form | throw (IO.userError "summed right form")
  let some leftCalleeNode := source.lookupExpression? leftCalleeId | throw (IO.userError "summed left callee")
  let some rightCalleeNode := source.lookupExpression? rightCalleeId | throw (IO.userError "summed right callee")
  let some leftReadNode := source.lookupExpression? leftReadId | throw (IO.userError "summed left read")
  let some rightReadNode := source.lookupExpression? rightReadId | throw (IO.userError "summed right read")
  let leftRead ← Tests.SourceCoreNamedBranch.observeRead source binder leftReadNode .word
  let rightRead ← Tests.SourceCoreNamedBranch.observeRead source binder rightReadNode .word
  let left ← observeConversion source .wordToInteger leftRead.node.id leftCalleeNode leftNode
  let right ← observeConversion source .wordToInteger rightRead.node.id rightCalleeNode rightNode
  let sumCallee ← Tests.SourceCoreOperatorCalls.observeNode source sumCalleeNode BuiltinFunctionId.integerAdd.type
  let sum ← Tests.SourceCoreOperatorCalls.observeNode source sumNode .integer
  let .reference sumName (.builtinFunction _) := sumCalleeNode.form | throw (IO.userError "summed sum callee form")
  let ⟨sumCalleeForm⟩ ← observed (sumCallee.node.form = .reference sumName (.builtinFunction .integerAdd))
    "summed sum callee"
  let ⟨sumForm⟩ ← observed (sum.node.form = .call sumCallee.node.id [left.value.node.id, right.value.node.id]
    (.builtinFunction .integerAdd)) "summed sum call"
  let ⟨inputs⟩ ← observed (source.inputs = [binder]) "summed inputs"
  let ⟨roots⟩ ← observed (source.roots = [.statement statement.id]) "summed roots shape"
  let ⟨statementFound⟩ ← observed (source.lookupStatement? statement.id = some statement) "summed statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some sum.node.id)) "summed statementForm"
  return ⟨binder, leftRead, rightRead, left, right, sumCallee, sum, sumName, sumCalleeForm, sumForm, statement,
    inputs, roots, statementFound, statementForm⟩

/-- `summed`'s body: the return of `integerAdd(wordToInteger(value), wordToInteger(value))`. -/
structure SummedShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  parts : SummedParts function.typedBody
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [.integer]
  binderScheme : parts.binder.scheme = .mono .word
  binderRequirements : parts.binder.schemeRequirements = []
  statementType : parts.statement.type = .integer

theorem SummedShape.statementTyping {function : CheckedFunction} {signature : ProgramFunctionSignature}
    (shape : SummedShape function signature) (signatures : ProgramSignatures) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.parts.statement.id] := statementRoots_injective (roots.symm.trans shape.parts.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type := .integer, hasValue := true, sawReturn := true, control := .returned}
  refine ⟨BodyFacts.singleton facts, rfl, ?_⟩
  intro lexical extension
  rw [shape.parts.inputs, shape.inputTypes] at extension
  cases extension with
  | cons scheme head tail =>
    cases tail
    have binders : TypeParameterBindersWellFormed lexical := by
      rw [TypeParameterBindersWellFormed, head.context_fields.2.2.1]
      simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
        Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
    have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
    have integer : TypeAdmissible lexical .integer := ⟨binders, .builtin .integer⟩
    have leftRead := shape.parts.leftRead.typed scheme shape.binderRequirements word head.local_self
      head.local_scheme_requirements_self
    have rightRead := shape.parts.rightRead.typed scheme shape.binderRequirements word head.local_self
      head.local_scheme_requirements_self
    have leftTyped := shape.parts.left.typed rfl integer leftRead
    have rightTyped := shape.parts.right.typed rfl integer rightRead
    have callee : DirectBuiltinCalleeValid function.typedBody shape.parts.sumCallee.node.id .integerAdd :=
      .intro (lookupExpression?_sound shape.parts.sumCallee.found) shape.parts.sumCalleeForm
        shape.parts.sumCallee.type shape.parts.sumCallee.requirements shape.parts.sumCallee.coercions
    have arguments : ExpressionsHaveTypes function.typedBody lexical
        [shape.parts.left.value.node.id, shape.parts.right.value.node.id] BuiltinFunctionId.integerAdd.parameterTypes :=
      .cons leftTyped (.cons rightTyped (.nil _))
    have typed : ExpressionHasType function.typedBody lexical shape.parts.sum.node.id shape.parts.sum.node.type := by
      refine .intro (lookupExpression?_sound shape.parts.sum.found)
        (shape.parts.sumForm ▸ ExpressionFormHasRawType.builtinCall callee arguments)
        shape.parts.sum.raw integer (shape.parts.sum.type.symm ▸ integer) ?_
      rw [shape.parts.sum.requirements, shape.parts.sum.coercions, shape.parts.sum.type]
      exact .ordinary (by intro id member; cases member) (.nil _) rfl
    rw [shape.parts.sum.type] at typed
    exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.parts.statementFound)
      shape.parts.statementForm typed shape.statementType)⟩

def observeSummed (function : CheckedFunction) (signature : ProgramFunctionSignature) :
    IO (SummedShape function signature) := do
  let parts ← observeSummedParts function.typedBody
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "summed parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "summed inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.integer]) "summed returns"
  let ⟨binderScheme⟩ ← observed (parts.binder.scheme = .mono .word) "summed binderScheme"
  let ⟨binderRequirements⟩ ← observed (parts.binder.schemeRequirements = []) "summed binderRequirements"
  let ⟨statementType⟩ ← observed (parts.statement.type = .integer) "summed statementType"
  return ⟨parts, parameters, inputTypes, returns, binderScheme, binderRequirements, statementType⟩

/-- The nodes of `zeroed`'s body: the read of its parameter, the call of the
opcode closure `iszero` that `std.opcodes` exports at it and the return of the
call, found by following the return statement's expression graph. -/
structure ZeroedParts (source : TypedSource) where
  binder : TypedBinder
  read : Tests.SourceCoreNamedBranch.Read source binder .word
  tested : Tests.SourceCoreBuiltinCalls.BuiltinCall source (.wordOpcode .iszero) read.node.id
  statement : StatementNode
  inputs : source.inputs = [binder]
  roots : source.roots = [.statement statement.id]
  statementFound : source.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some tested.value.node.id)

def observeZeroedParts (source : TypedSource) : IO (ZeroedParts source) := do
  let [binder] := source.inputs | throw (IO.userError "zeroed input")
  let [.statement statementId] := source.roots | throw (IO.userError "zeroed roots")
  let some statement := source.lookupStatement? statementId | throw (IO.userError "zeroed statement")
  let .returnStmt (some valueId) := statement.form | throw (IO.userError "zeroed return")
  let some valueNode := source.lookupExpression? valueId | throw (IO.userError "zeroed call node")
  let .call calleeId [readId] _ := valueNode.form | throw (IO.userError "zeroed call form")
  let some calleeNode := source.lookupExpression? calleeId | throw (IO.userError "zeroed callee")
  let some readNode := source.lookupExpression? readId | throw (IO.userError "zeroed read")
  let read ← Tests.SourceCoreNamedBranch.observeRead source binder readNode .word
  let tested ← observeConversion source (.wordOpcode .iszero) read.node.id calleeNode valueNode
  let ⟨inputs⟩ ← observed (source.inputs = [binder]) "zeroed inputs"
  let ⟨roots⟩ ← observed (source.roots = [.statement statement.id]) "zeroed roots shape"
  let ⟨statementFound⟩ ← observed (source.lookupStatement? statement.id = some statement) "zeroed statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some tested.value.node.id))
    "zeroed statementForm"
  return ⟨binder, read, tested, statement, inputs, roots, statementFound, statementForm⟩

/-- `zeroed`'s body: the return of `iszero(value)`. -/
structure ZeroedShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  parts : ZeroedParts function.typedBody
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [.word]
  binderScheme : parts.binder.scheme = .mono .word
  binderRequirements : parts.binder.schemeRequirements = []
  statementType : parts.statement.type = .word

theorem ZeroedShape.statementTyping {function : CheckedFunction} {signature : ProgramFunctionSignature}
    (shape : ZeroedShape function signature) (signatures : ProgramSignatures) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.parts.statement.id] :=
    statementRoots_injective (roots.symm.trans shape.parts.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type := .word, hasValue := true, sawReturn := true, control := .returned}
  refine ⟨BodyFacts.singleton facts, rfl, ?_⟩
  intro lexical extension
  rw [shape.parts.inputs, shape.inputTypes] at extension
  cases extension with
  | cons scheme head tail =>
    cases tail
    have binders : TypeParameterBindersWellFormed lexical := by
      rw [TypeParameterBindersWellFormed, head.context_fields.2.2.1]
      simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
        Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
    have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
    have read := shape.parts.read.typed scheme shape.binderRequirements word head.local_self
      head.local_scheme_requirements_self
    have tested := shape.parts.tested.typed rfl word read
    exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.parts.statementFound)
      shape.parts.statementForm tested shape.statementType)⟩

def observeZeroed (function : CheckedFunction) (signature : ProgramFunctionSignature) :
    IO (ZeroedShape function signature) := do
  let parts ← observeZeroedParts function.typedBody
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "zeroed parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "zeroed inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.word]) "zeroed returns"
  let ⟨binderScheme⟩ ← observed (parts.binder.scheme = .mono .word) "zeroed binderScheme"
  let ⟨binderRequirements⟩ ← observed (parts.binder.schemeRequirements = []) "zeroed binderRequirements"
  let ⟨statementType⟩ ← observed (parts.statement.type = .word) "zeroed statementType"
  return ⟨parts, parameters, inputTypes, returns, binderScheme, binderRequirements, statementType⟩

/-- The nodes of `inverted`'s body: the declaration of its local mapping
`table`, `table[value] ~=`, whose key reads the parameter, and the return of
`table[value]`, found by following the statement graph. -/
structure InvertedParts (source : TypedSource) where
  binder : TypedBinder
  table : TypedBinder
  keyRead : Tests.SourceCoreNamedBranch.Read source binder .word
  baseRead : Tests.SourceCoreNamedBranch.Read source table (.mapping .word .word)
  indexKey : Tests.SourceCoreNamedBranch.Read source binder .word
  index : ExpressionNode
  declared : StatementNode
  flip : StatementNode
  resolution : AssignmentResolution
  returned : StatementNode
  inputs : source.inputs = [binder]
  roots : source.roots = [.statement declared.id, .statement flip.id, .statement returned.id]
  declaredFound : source.lookupStatement? declared.id = some declared
  declaredForm : declared.form = .letDecl table none
  flipFound : source.lookupStatement? flip.id = some flip
  flipForm : flip.form = .assignBitNot resolution
  targetRoot : resolution.target.root = table.id
  targetProjections : resolution.target.projections = [.index keyRead.node.id]
  targetType : resolution.target.type = .word
  indexFound : source.lookupExpression? index.id = some index
  indexForm : index.form = .index baseRead.node.id indexKey.node.id
  indexRaw : index.rawType = .word
  indexType : index.type = .word
  indexRequirements : index.requirements = []
  indexCoercions : index.coercions = []
  returnedFound : source.lookupStatement? returned.id = some returned
  returnedForm : returned.form = .returnStmt (some index.id)

def observeInvertedParts (source : TypedSource) : IO (InvertedParts source) := do
  let [binder] := source.inputs | throw (IO.userError "inverted input")
  let [.statement declaredId, .statement flipId, .statement returnedId] := source.roots
    | throw (IO.userError "inverted roots")
  let some declared := source.lookupStatement? declaredId | throw (IO.userError "inverted let")
  let some flip := source.lookupStatement? flipId | throw (IO.userError "inverted flip")
  let some returned := source.lookupStatement? returnedId | throw (IO.userError "inverted return")
  let .letDecl table none := declared.form | throw (IO.userError "inverted let form")
  let .assignBitNot resolution := flip.form | throw (IO.userError "inverted flip form")
  let [.index keyId] := resolution.target.projections | throw (IO.userError "inverted target projections")
  let .returnStmt (some indexId) := returned.form | throw (IO.userError "inverted return form")
  let some keyNode := source.lookupExpression? keyId | throw (IO.userError "inverted key")
  let some index := source.lookupExpression? indexId | throw (IO.userError "inverted index")
  let .index baseId indexKeyId := index.form | throw (IO.userError "inverted index form")
  let some baseNode := source.lookupExpression? baseId | throw (IO.userError "inverted base")
  let some indexKeyNode := source.lookupExpression? indexKeyId | throw (IO.userError "inverted index key")
  let keyRead ← Tests.SourceCoreNamedBranch.observeRead source binder keyNode .word
  let baseRead ← Tests.SourceCoreNamedBranch.observeRead source table baseNode (.mapping .word .word)
  let indexKey ← Tests.SourceCoreNamedBranch.observeRead source binder indexKeyNode .word
  let ⟨inputs⟩ ← observed (source.inputs = [binder]) "inverted inputs"
  let ⟨roots⟩ ← observed (source.roots = [.statement declared.id, .statement flip.id, .statement returned.id])
    "inverted roots shape"
  let ⟨declaredFound⟩ ← observed (source.lookupStatement? declared.id = some declared) "inverted declaredFound"
  let ⟨declaredForm⟩ ← observed (declared.form = .letDecl table none) "inverted declaredForm"
  let ⟨flipFound⟩ ← observed (source.lookupStatement? flip.id = some flip) "inverted flipFound"
  let ⟨flipForm⟩ ← observed (flip.form = .assignBitNot resolution) "inverted flipForm"
  let ⟨targetRoot⟩ ← observed (resolution.target.root = table.id) "inverted targetRoot"
  let ⟨targetProjections⟩ ← observed (resolution.target.projections = [.index keyRead.node.id])
    "inverted targetProjections"
  let ⟨targetType⟩ ← observed (resolution.target.type = .word) "inverted targetType"
  let ⟨indexFound⟩ ← observed (source.lookupExpression? index.id = some index) "inverted indexFound"
  let ⟨indexForm⟩ ← observed (index.form = .index baseRead.node.id indexKey.node.id) "inverted indexForm"
  let ⟨indexRaw⟩ ← observed (index.rawType = .word) "inverted indexRaw"
  let ⟨indexType⟩ ← observed (index.type = .word) "inverted indexType"
  let ⟨indexRequirements⟩ ← observed (index.requirements = []) "inverted indexRequirements"
  let ⟨indexCoercions⟩ ← observed (index.coercions = []) "inverted indexCoercions"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "inverted returnedFound"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some index.id)) "inverted returnedForm"
  return ⟨binder, table, keyRead, baseRead, indexKey, index, declared, flip, resolution, returned, inputs, roots,
    declaredFound, declaredForm, flipFound, flipForm, targetRoot, targetProjections, targetType, indexFound,
    indexForm, indexRaw, indexType, indexRequirements, indexCoercions, returnedFound, returnedForm⟩

/-- `inverted`'s body: `let table: mapping(Word => Word)`, `table[value] ~=` through the local's index and
the return of `table[value]`. -/
structure InvertedShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  parts : InvertedParts function.typedBody
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [.word]
  binderScheme : parts.binder.scheme = .mono .word
  binderRequirements : parts.binder.schemeRequirements = []
  tableScheme : parts.table.scheme = .mono (.mapping .word .word)
  tableRequirements : parts.table.schemeRequirements = []
  tableOwner : parts.table.id.owner = function.typedBody.owner
  tableDistinct : parts.table.id ≠ parts.binder.id
  declaredType : parts.declared.type = .unit
  flipType : parts.flip.type = .unit
  returnedType : parts.returned.type = .word
  flipRequirements : parts.resolution.requirements = []

theorem InvertedShape.statementTyping {function : CheckedFunction} {signature : ProgramFunctionSignature}
    (shape : InvertedShape function signature) (signatures : ProgramSignatures) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.parts.declared.id, shape.parts.flip.id, shape.parts.returned.id] :=
    statementRoots_injective (roots.symm.trans shape.parts.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type := .word, hasValue := true, sawReturn := true, control := .returned}
  let ordinary : StatementFacts := {type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit}
  refine ⟨BodyFacts.cons ordinary (BodyFacts.cons ordinary (BodyFacts.singleton facts)), rfl, ?_⟩
  intro lexical extension
  rw [shape.parts.inputs, shape.inputTypes] at extension
  cases extension with
  | cons scheme head tail =>
    cases tail
    have binders : TypeParameterBindersWellFormed lexical := by
      rw [TypeParameterBindersWellFormed, head.context_fields.2.2.1]
      simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
        Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
    have mapping : TypeAdmissible lexical (.mapping .word .word) :=
      ⟨binders, .mapping (.builtin .word) (.builtin .word)⟩
    let locals := lexical.withLocal shape.parts.table.id shape.parts.table.scheme shape.parts.table.schemeRequirements
    have tableExtended : BinderExtends function.typedBody.owner lexical shape.parts.table locals := by
      apply BinderExtends.intro
      · exact {
          owned := shape.tableOwner
          scheme := shape.tableScheme.symm ▸ SchemeWellFormed.monoAdmissible mapping
          quantified_fresh := by rw [shape.tableScheme]; simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]
          monomorphic_requirements_empty := fun _ => shape.tableRequirements }
      · cases head
        simp [LocalFresh, Context.withLocal, checkedBodyContext, declarationContext,
          Context.ofSignatures, Context.forDeclaration, Context.withAssumptions,
          Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.tableDistinct]
    have localWord : TypeAdmissible locals .word := ⟨binders, .builtin .word⟩
    have localMapping : TypeAdmissible locals (.mapping .word .word) :=
      ⟨binders, .mapping (.builtin .word) (.builtin .word)⟩
    have declaredTyped : StatementHasType function.typedBody ⟨.word, 0⟩ lexical shape.parts.declared.id locals
        ordinary := by
      apply StatementHasType.letUninitialized (lookupStatement?_sound shape.parts.declaredFound)
        shape.parts.declaredForm
      · rw [shape.tableScheme]; rfl
      · rw [shape.tableScheme]; rfl
      · exact tableExtended
      · exact shape.declaredType
    have parameterLookup : locals.LocalLookup shape.parts.binder.id shape.parts.binder.scheme :=
      .tail shape.tableDistinct head.local_self
    have parameterRequirements :
        locals.LocalSchemeRequirementsLookup shape.parts.binder.id shape.parts.binder.schemeRequirements :=
      .tail shape.tableDistinct head.local_scheme_requirements_self
    have keyTyped := shape.parts.keyRead.typed scheme shape.binderRequirements localWord parameterLookup
      parameterRequirements
    have writable : WritableLocal locals shape.parts.resolution.target.root (.mapping .word .word) := by
      rw [shape.parts.targetRoot]
      exact .intro tableExtended.local_self (shape.tableScheme.symm ▸ SchemeWellFormed.monoAdmissible localMapping)
        (by rw [shape.tableScheme]; rfl) (by rw [shape.tableScheme]; rfl)
    have flipValid : SourceBitNotAssignmentValid function.typedBody locals shape.parts.resolution :=
      .intro (.intro writable (by rw [shape.parts.targetProjections]; exact .index keyTyped (.nil _))
        shape.parts.targetType) .word shape.flipRequirements
    have flippedTyped : StatementHasType function.typedBody ⟨.word, 0⟩ locals shape.parts.flip.id locals ordinary :=
      .assignBitNot (lookupStatement?_sound shape.parts.flipFound) shape.parts.flipForm flipValid shape.flipType
    have baseTyped := shape.parts.baseRead.typed shape.tableScheme shape.tableRequirements localMapping
      tableExtended.local_self tableExtended.local_scheme_requirements_self
    have indexKeyTyped := shape.parts.indexKey.typed scheme shape.binderRequirements localWord parameterLookup
      parameterRequirements
    have indexTyped : ExpressionHasType function.typedBody locals shape.parts.index.id shape.parts.index.type := by
      refine .intro (lookupExpression?_sound shape.parts.indexFound)
        (shape.parts.indexForm ▸ ExpressionFormHasRawType.index baseTyped indexKeyTyped) shape.parts.indexRaw
        localWord (Eq.mp (congrArg (TypeAdmissible locals) shape.parts.indexType.symm) localWord) ?_
      rw [shape.parts.indexRequirements, shape.parts.indexCoercions, shape.parts.indexType]
      exact .ordinary (by intro id member; cases member) (.nil _) rfl
    rw [shape.parts.indexType] at indexTyped
    exact ⟨_, .cons declaredTyped (.cons flippedTyped (.singleton (.returnValue
      (lookupStatement?_sound shape.parts.returnedFound) shape.parts.returnedForm indexTyped shape.returnedType)))⟩

def observeInverted (function : CheckedFunction) (signature : ProgramFunctionSignature) :
    IO (InvertedShape function signature) := do
  let parts ← observeInvertedParts function.typedBody
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "inverted parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "inverted inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.word]) "inverted returns"
  let ⟨binderScheme⟩ ← observed (parts.binder.scheme = .mono .word) "inverted binderScheme"
  let ⟨binderRequirements⟩ ← observed (parts.binder.schemeRequirements = []) "inverted binderRequirements"
  let ⟨tableScheme⟩ ← observed (parts.table.scheme = .mono (.mapping .word .word)) "inverted tableScheme"
  let ⟨tableRequirements⟩ ← observed (parts.table.schemeRequirements = []) "inverted tableRequirements"
  let ⟨tableOwner⟩ ← observed (parts.table.id.owner = function.typedBody.owner) "inverted tableOwner"
  let ⟨tableDistinct⟩ ← observed (parts.table.id ≠ parts.binder.id) "inverted tableDistinct"
  let ⟨declaredType⟩ ← observed (parts.declared.type = .unit) "inverted declaredType"
  let ⟨flipType⟩ ← observed (parts.flip.type = .unit) "inverted flipType"
  let ⟨returnedType⟩ ← observed (parts.returned.type = .word) "inverted returnedType"
  let ⟨flipRequirements⟩ ← observed (parts.resolution.requirements = []) "inverted flipRequirements"
  return ⟨parts, parameters, inputTypes, returns, binderScheme, binderRequirements, tableScheme, tableRequirements,
    tableOwner, tableDistinct, declaredType, flipType, returnedType, flipRequirements⟩

/-- The nodes of `broken`'s body: a `while` loop whose condition is the builtin
`true` and whose body is a `break`, and the return of the parameter, found by
following the statement graph. -/
structure BrokenParts (source : TypedSource) where
  binder : TypedBinder
  read : Tests.SourceCoreNamedBranch.Read source binder .word
  loop : StatementNode
  condition : ExpressionNode
  name : String
  jump : StatementNode
  returned : StatementNode
  inputs : source.inputs = [binder]
  roots : source.roots = [.statement loop.id, .statement returned.id]
  loopFound : source.lookupStatement? loop.id = some loop
  loopForm : loop.form = .whileLoop condition.id [jump.id]
  conditionFound : source.lookupExpression? condition.id = some condition
  conditionForm : condition.form = .reference name (.builtinBoolean true)
  conditionRaw : condition.rawType = .bool
  conditionType : condition.type = .bool
  conditionRequirements : condition.requirements = []
  conditionCoercions : condition.coercions = []
  jumpFound : source.lookupStatement? jump.id = some jump
  jumpForm : jump.form = .breakStmt
  returnedFound : source.lookupStatement? returned.id = some returned
  returnedForm : returned.form = .returnStmt (some read.node.id)

def observeBrokenParts (source : TypedSource) : IO (BrokenParts source) := do
  let [binder] := source.inputs | throw (IO.userError "broken input")
  let [.statement loopId, .statement returnedId] := source.roots | throw (IO.userError "broken roots")
  let some loop := source.lookupStatement? loopId | throw (IO.userError "broken loop")
  let some returned := source.lookupStatement? returnedId | throw (IO.userError "broken return")
  let .whileLoop conditionId [jumpId] := loop.form | throw (IO.userError "broken loop form")
  let some condition := source.lookupExpression? conditionId | throw (IO.userError "broken condition")
  let .reference name (.builtinBoolean true) := condition.form | throw (IO.userError "broken condition form")
  let some jump := source.lookupStatement? jumpId | throw (IO.userError "broken jump")
  let .returnStmt (some readId) := returned.form | throw (IO.userError "broken return form")
  let some readNode := source.lookupExpression? readId | throw (IO.userError "broken read")
  let read ← Tests.SourceCoreNamedBranch.observeRead source binder readNode .word
  let ⟨inputs⟩ ← observed (source.inputs = [binder]) "broken inputs"
  let ⟨roots⟩ ← observed (source.roots = [.statement loop.id, .statement returned.id]) "broken roots shape"
  let ⟨loopFound⟩ ← observed (source.lookupStatement? loop.id = some loop) "broken loopFound"
  let ⟨loopForm⟩ ← observed (loop.form = .whileLoop condition.id [jump.id]) "broken loopForm"
  let ⟨conditionFound⟩ ← observed (source.lookupExpression? condition.id = some condition) "broken conditionFound"
  let ⟨conditionForm⟩ ← observed (condition.form = .reference name (.builtinBoolean true)) "broken conditionForm"
  let ⟨conditionRaw⟩ ← observed (condition.rawType = .bool) "broken conditionRaw"
  let ⟨conditionType⟩ ← observed (condition.type = .bool) "broken conditionType"
  let ⟨conditionRequirements⟩ ← observed (condition.requirements = []) "broken conditionRequirements"
  let ⟨conditionCoercions⟩ ← observed (condition.coercions = []) "broken conditionCoercions"
  let ⟨jumpFound⟩ ← observed (source.lookupStatement? jump.id = some jump) "broken jumpFound"
  let ⟨jumpForm⟩ ← observed (jump.form = .breakStmt) "broken jumpForm"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "broken returnedFound"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some read.node.id)) "broken returnedForm"
  return ⟨binder, read, loop, condition, name, jump, returned, inputs, roots, loopFound, loopForm, conditionFound,
    conditionForm, conditionRaw, conditionType, conditionRequirements, conditionCoercions, jumpFound, jumpForm,
    returnedFound, returnedForm⟩

/-- `broken`'s body: `while (true) { break; }` and the return of the parameter. -/
structure BrokenShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  parts : BrokenParts function.typedBody
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [.word]
  binderRequirements : parts.binder.schemeRequirements = []
  loopType : parts.loop.type = .unit
  jumpType : parts.jump.type = .unit
  returnedType : parts.returned.type = .word

theorem BrokenShape.statementTyping {function : CheckedFunction} {signature : ProgramFunctionSignature}
    (shape : BrokenShape function signature) (signatures : ProgramSignatures) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.parts.loop.id, shape.parts.returned.id] :=
    statementRoots_injective (roots.symm.trans shape.parts.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type := .word, hasValue := true, sawReturn := true, control := .returned}
  let ordinary : StatementFacts := {type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit}
  refine ⟨BodyFacts.cons ordinary (BodyFacts.singleton facts), rfl, ?_⟩
  intro lexical extension
  rw [shape.parts.inputs, shape.inputTypes] at extension
  cases extension with
  | cons scheme head tail =>
    cases tail
    have binders : TypeParameterBindersWellFormed lexical := by
      rw [TypeParameterBindersWellFormed, head.context_fields.2.2.1]
      simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
        Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
    have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
    have boolean : TypeAdmissible lexical .bool := ⟨binders, .builtin .bool⟩
    have conditionTyped : ExpressionHasType function.typedBody lexical shape.parts.condition.id
        shape.parts.condition.type := by
      apply ExpressionHasType.ofOrdinary (rawType := .bool) (owned := [])
        (lookupExpression?_sound shape.parts.conditionFound)
      · rw [shape.parts.conditionForm]
        exact .reference (.builtinBoolean true)
      · exact boolean
      · rw [shape.parts.conditionType]
        exact boolean
      · intro id member
        cases member
      · rw [shape.parts.conditionCoercions, shape.parts.conditionType]
        exact .nil _
      · rw [shape.parts.conditionRequirements, shape.parts.conditionCoercions]
        rfl
    rw [shape.parts.conditionType] at conditionTyped
    have jumpTyped : StatementHasType function.typedBody (ControlContext.enterLoop ⟨.word, 0⟩) lexical
        shape.parts.jump.id lexical {type := .unit, hasValue := false, sawReturn := false, control := .breaking} :=
      .breakStmt (lookupStatement?_sound shape.parts.jumpFound) shape.parts.jumpForm
        (by simp [ControlContext.loopAllowed, ControlContext.enterLoop]) shape.jumpType
    have loopTyped : StatementHasType function.typedBody ⟨.word, 0⟩ lexical shape.parts.loop.id lexical ordinary :=
      .whileLoop (lookupStatement?_sound shape.parts.loopFound) shape.parts.loopForm conditionTyped
        (.singleton jumpTyped) shape.loopType
    have read := shape.parts.read.typed scheme shape.binderRequirements word head.local_self
      head.local_scheme_requirements_self
    exact ⟨_, .cons loopTyped (.singleton (.returnValue (lookupStatement?_sound shape.parts.returnedFound)
      shape.parts.returnedForm read shape.returnedType))⟩

def observeBroken (function : CheckedFunction) (signature : ProgramFunctionSignature) :
    IO (BrokenShape function signature) := do
  let parts ← observeBrokenParts function.typedBody
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "broken parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "broken inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.word]) "broken returns"
  let ⟨binderRequirements⟩ ← observed (parts.binder.schemeRequirements = []) "broken binderRequirements"
  let ⟨loopType⟩ ← observed (parts.loop.type = .unit) "broken loopType"
  let ⟨jumpType⟩ ← observed (parts.jump.type = .unit) "broken jumpType"
  let ⟨returnedType⟩ ← observed (parts.returned.type = .word) "broken returnedType"
  return ⟨parts, parameters, inputTypes, returns, binderRequirements, loopType, jumpType, returnedType⟩

/-- The nodes of `counted`'s body: a `for` loop whose header declares the
`bool` local `go` at the builtin `true`, tests `go` and assigns it the builtin
`false` after each iteration, and whose body is a `continue`, and the return of
the parameter, found by following the statement graph. -/
structure CountedParts (source : TypedSource) where
  binder : TypedBinder
  read : Tests.SourceCoreNamedBranch.Read source binder .word
  go : TypedBinder
  test : Tests.SourceCoreNamedBranch.Read source go .bool
  loop : StatementNode
  start : ExpressionNode
  startName : String
  resolution : AssignmentResolution
  stop : ExpressionNode
  stopName : String
  jump : StatementNode
  returned : StatementNode
  inputs : source.inputs = [binder]
  roots : source.roots = [.statement loop.id, .statement returned.id]
  loopFound : source.lookupStatement? loop.id = some loop
  loopForm : loop.form = .forLoop [.letDecl go (some start.id)] test.node.id
    [.assignValue resolution .equal stop.id] [jump.id]
  startFound : source.lookupExpression? start.id = some start
  startForm : start.form = .reference startName (.builtinBoolean true)
  startRaw : start.rawType = .bool
  startType : start.type = .bool
  startRequirements : start.requirements = []
  startCoercions : start.coercions = []
  targetRoot : resolution.target.root = go.id
  targetProjections : resolution.target.projections = []
  targetType : resolution.target.type = .bool
  stopFound : source.lookupExpression? stop.id = some stop
  stopForm : stop.form = .reference stopName (.builtinBoolean false)
  stopRaw : stop.rawType = .bool
  stopType : stop.type = .bool
  stopRequirements : stop.requirements = []
  stopCoercions : stop.coercions = []
  jumpFound : source.lookupStatement? jump.id = some jump
  jumpForm : jump.form = .continueStmt
  returnedFound : source.lookupStatement? returned.id = some returned
  returnedForm : returned.form = .returnStmt (some read.node.id)

def observeCountedParts (source : TypedSource) : IO (CountedParts source) := do
  let [binder] := source.inputs | throw (IO.userError "counted input")
  let [.statement loopId, .statement returnedId] := source.roots | throw (IO.userError "counted roots")
  let some loop := source.lookupStatement? loopId | throw (IO.userError "counted loop")
  let some returned := source.lookupStatement? returnedId | throw (IO.userError "counted return")
  let .forLoop [.letDecl go (some startId)] testId [.assignValue resolution .equal stopId] [jumpId] := loop.form
    | throw (IO.userError "counted loop form")
  let some start := source.lookupExpression? startId | throw (IO.userError "counted start")
  let .reference startName (.builtinBoolean true) := start.form | throw (IO.userError "counted start form")
  let some testNode := source.lookupExpression? testId | throw (IO.userError "counted test")
  let some stop := source.lookupExpression? stopId | throw (IO.userError "counted stop")
  let .reference stopName (.builtinBoolean false) := stop.form | throw (IO.userError "counted stop form")
  let some jump := source.lookupStatement? jumpId | throw (IO.userError "counted jump")
  let .returnStmt (some readId) := returned.form | throw (IO.userError "counted return form")
  let some readNode := source.lookupExpression? readId | throw (IO.userError "counted read")
  let read ← Tests.SourceCoreNamedBranch.observeRead source binder readNode .word
  let test ← Tests.SourceCoreNamedBranch.observeRead source go testNode .bool
  let ⟨inputs⟩ ← observed (source.inputs = [binder]) "counted inputs"
  let ⟨roots⟩ ← observed (source.roots = [.statement loop.id, .statement returned.id]) "counted roots shape"
  let ⟨loopFound⟩ ← observed (source.lookupStatement? loop.id = some loop) "counted loopFound"
  let ⟨loopForm⟩ ← observed (loop.form = .forLoop [.letDecl go (some start.id)] test.node.id
    [.assignValue resolution .equal stop.id] [jump.id]) "counted loopForm"
  let ⟨startFound⟩ ← observed (source.lookupExpression? start.id = some start) "counted startFound"
  let ⟨startForm⟩ ← observed (start.form = .reference startName (.builtinBoolean true)) "counted startForm"
  let ⟨startRaw⟩ ← observed (start.rawType = .bool) "counted startRaw"
  let ⟨startType⟩ ← observed (start.type = .bool) "counted startType"
  let ⟨startRequirements⟩ ← observed (start.requirements = []) "counted startRequirements"
  let ⟨startCoercions⟩ ← observed (start.coercions = []) "counted startCoercions"
  let ⟨targetRoot⟩ ← observed (resolution.target.root = go.id) "counted targetRoot"
  let ⟨targetProjections⟩ ← observed (resolution.target.projections = []) "counted targetProjections"
  let ⟨targetType⟩ ← observed (resolution.target.type = .bool) "counted targetType"
  let ⟨stopFound⟩ ← observed (source.lookupExpression? stop.id = some stop) "counted stopFound"
  let ⟨stopForm⟩ ← observed (stop.form = .reference stopName (.builtinBoolean false)) "counted stopForm"
  let ⟨stopRaw⟩ ← observed (stop.rawType = .bool) "counted stopRaw"
  let ⟨stopType⟩ ← observed (stop.type = .bool) "counted stopType"
  let ⟨stopRequirements⟩ ← observed (stop.requirements = []) "counted stopRequirements"
  let ⟨stopCoercions⟩ ← observed (stop.coercions = []) "counted stopCoercions"
  let ⟨jumpFound⟩ ← observed (source.lookupStatement? jump.id = some jump) "counted jumpFound"
  let ⟨jumpForm⟩ ← observed (jump.form = .continueStmt) "counted jumpForm"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "counted returnedFound"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some read.node.id)) "counted returnedForm"
  return ⟨binder, read, go, test, loop, start, startName, resolution, stop, stopName, jump, returned, inputs,
    roots, loopFound, loopForm, startFound, startForm, startRaw, startType, startRequirements, startCoercions,
    targetRoot, targetProjections, targetType, stopFound, stopForm, stopRaw, stopType, stopRequirements,
    stopCoercions, jumpFound, jumpForm, returnedFound, returnedForm⟩

/-- `counted`'s body: `for (let go: bool = true; go; go = false) { continue; }`
and the return of the parameter. -/
structure CountedShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  parts : CountedParts function.typedBody
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [.word]
  binderRequirements : parts.binder.schemeRequirements = []
  goScheme : parts.go.scheme = .mono .bool
  goRequirements : parts.go.schemeRequirements = []
  goOwner : parts.go.id.owner = function.typedBody.owner
  goDistinct : parts.go.id ≠ parts.binder.id
  loopType : parts.loop.type = .unit
  jumpType : parts.jump.type = .unit
  returnedType : parts.returned.type = .word
  assignmentRequirements : parts.resolution.requirements = []

theorem CountedShape.statementTyping {function : CheckedFunction} {signature : ProgramFunctionSignature}
    (shape : CountedShape function signature) (signatures : ProgramSignatures) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.parts.loop.id, shape.parts.returned.id] :=
    statementRoots_injective (roots.symm.trans shape.parts.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type := .word, hasValue := true, sawReturn := true, control := .returned}
  let ordinary : StatementFacts := {type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit}
  refine ⟨BodyFacts.cons ordinary (BodyFacts.singleton facts), rfl, ?_⟩
  intro lexical extension
  rw [shape.parts.inputs, shape.inputTypes] at extension
  cases extension with
  | cons scheme head tail =>
    cases tail
    have binders : TypeParameterBindersWellFormed lexical := by
      rw [TypeParameterBindersWellFormed, head.context_fields.2.2.1]
      simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
        Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
    have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
    have boolean : TypeAdmissible lexical .bool := ⟨binders, .builtin .bool⟩
    have startTyped : ExpressionHasType function.typedBody lexical shape.parts.start.id shape.parts.start.type := by
      apply ExpressionHasType.ofOrdinary (rawType := .bool) (owned := [])
        (lookupExpression?_sound shape.parts.startFound)
      · rw [shape.parts.startForm]
        exact .reference (.builtinBoolean true)
      · exact boolean
      · rw [shape.parts.startType]
        exact boolean
      · intro id member
        cases member
      · rw [shape.parts.startCoercions, shape.parts.startType]
        exact .nil _
      · rw [shape.parts.startRequirements, shape.parts.startCoercions]
        rfl
    rw [shape.parts.startType] at startTyped
    let locals := lexical.withLocal shape.parts.go.id shape.parts.go.scheme shape.parts.go.schemeRequirements
    have goExtended : BinderExtends function.typedBody.owner lexical shape.parts.go locals := by
      apply BinderExtends.intro
      · exact {
          owned := shape.goOwner
          scheme := shape.goScheme.symm ▸ SchemeWellFormed.monoAdmissible boolean
          quantified_fresh := by rw [shape.goScheme]; simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]
          monomorphic_requirements_empty := fun _ => shape.goRequirements }
      · cases head
        simp [LocalFresh, Context.withLocal, checkedBodyContext, declarationContext,
          Context.ofSignatures, Context.forDeclaration, Context.withAssumptions,
          Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.goDistinct]
    have localBoolean : TypeAdmissible locals .bool := ⟨binders, .builtin .bool⟩
    have testTyped := shape.parts.test.typed shape.goScheme shape.goRequirements localBoolean goExtended.local_self
      goExtended.local_scheme_requirements_self
    have stopTyped : ExpressionHasType function.typedBody locals shape.parts.stop.id shape.parts.stop.type := by
      apply ExpressionHasType.ofOrdinary (rawType := .bool) (owned := [])
        (lookupExpression?_sound shape.parts.stopFound)
      · rw [shape.parts.stopForm]
        exact .reference (.builtinBoolean false)
      · exact localBoolean
      · rw [shape.parts.stopType]
        exact localBoolean
      · intro id member
        cases member
      · rw [shape.parts.stopCoercions, shape.parts.stopType]
        exact .nil _
      · rw [shape.parts.stopRequirements, shape.parts.stopCoercions]
        rfl
    rw [shape.parts.stopType] at stopTyped
    have writable : WritableLocal locals shape.parts.resolution.target.root .bool := by
      rw [shape.parts.targetRoot]
      exact .intro goExtended.local_self (shape.goScheme.symm ▸ SchemeWellFormed.monoAdmissible localBoolean)
        (by rw [shape.goScheme]; rfl) (by rw [shape.goScheme]; rfl)
    have assignmentTyped : SourceAssignmentHasType function.typedBody locals shape.parts.resolution .equal
        shape.parts.stop.id :=
      .equal (.intro writable (by rw [shape.parts.targetProjections]; exact .nil _) shape.parts.targetType) stopTyped
        shape.assignmentRequirements
    have jumpTyped : StatementHasType function.typedBody (ControlContext.enterLoop ⟨.word, 0⟩) locals
        shape.parts.jump.id locals {type := .unit, hasValue := false, sawReturn := false, control := .continuing} :=
      .continueStmt (lookupStatement?_sound shape.parts.jumpFound) shape.parts.jumpForm
        (by simp [ControlContext.loopAllowed, ControlContext.enterLoop]) shape.jumpType
    have initialTyped : ForItemsHaveType function.typedBody ⟨.word, 0⟩ lexical
        [.letDecl shape.parts.go (some shape.parts.start.id)] locals :=
      .cons (.letInitialized (by simpa only [shape.goScheme, TypeSystem.Scheme.mono] using startTyped)
        (by rw [shape.goScheme]; rfl) (by rw [shape.goScheme]; rfl) goExtended) (.nil _ _)
    have loopTyped : StatementHasType function.typedBody ⟨.word, 0⟩ lexical shape.parts.loop.id lexical ordinary :=
      .forLoop (lookupStatement?_sound shape.parts.loopFound) shape.parts.loopForm initialTyped testTyped
        (.singleton jumpTyped) (.cons (.assignValue assignmentTyped) (.nil _ _)) shape.loopType
    have read := shape.parts.read.typed scheme shape.binderRequirements word head.local_self
      head.local_scheme_requirements_self
    exact ⟨_, .cons loopTyped (.singleton (.returnValue (lookupStatement?_sound shape.parts.returnedFound)
      shape.parts.returnedForm read shape.returnedType))⟩

def observeCounted (function : CheckedFunction) (signature : ProgramFunctionSignature) :
    IO (CountedShape function signature) := do
  let parts ← observeCountedParts function.typedBody
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "counted parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "counted inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.word]) "counted returns"
  let ⟨binderRequirements⟩ ← observed (parts.binder.schemeRequirements = []) "counted binderRequirements"
  let ⟨goScheme⟩ ← observed (parts.go.scheme = .mono .bool) "counted goScheme"
  let ⟨goRequirements⟩ ← observed (parts.go.schemeRequirements = []) "counted goRequirements"
  let ⟨goOwner⟩ ← observed (parts.go.id.owner = function.typedBody.owner) "counted goOwner"
  let ⟨goDistinct⟩ ← observed (parts.go.id ≠ parts.binder.id) "counted goDistinct"
  let ⟨loopType⟩ ← observed (parts.loop.type = .unit) "counted loopType"
  let ⟨jumpType⟩ ← observed (parts.jump.type = .unit) "counted jumpType"
  let ⟨returnedType⟩ ← observed (parts.returned.type = .word) "counted returnedType"
  let ⟨assignmentRequirements⟩ ← observed (parts.resolution.requirements = []) "counted assignmentRequirements"
  return ⟨parts, parameters, inputTypes, returns, binderRequirements, goScheme, goRequirements, goOwner, goDistinct,
    loopType, jumpType, returnedType, assignmentRequirements⟩

/-- The nodes of `tripled`'s body: three reads of its parameter, the tuple of
them and its return, found by following the statement graph. -/
structure TripledParts (source : TypedSource) where
  binder : TypedBinder
  first : Tests.SourceCoreNamedBranch.Read source binder .word
  second : Tests.SourceCoreNamedBranch.Read source binder .word
  third : Tests.SourceCoreNamedBranch.Read source binder .word
  tuple : ExpressionNode
  statement : StatementNode
  inputs : source.inputs = [binder]
  roots : source.roots = [.statement statement.id]
  statementFound : source.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some tuple.id)
  tupleFound : source.lookupExpression? tuple.id = some tuple
  tupleForm : tuple.form = .tuple [first.node.id, second.node.id, third.node.id]
  tupleRaw : tuple.rawType = TypeSystem.Ty.productMany [.word, .word, .word]
  tupleType : tuple.type = TypeSystem.Ty.productMany [.word, .word, .word]
  tupleRequirements : tuple.requirements = []
  tupleCoercions : tuple.coercions = []

def observeTripledParts (source : TypedSource) : IO (TripledParts source) := do
  let [binder] := source.inputs | throw (IO.userError "tripled input")
  let [.statement statementId] := source.roots | throw (IO.userError "tripled roots")
  let some statement := source.lookupStatement? statementId | throw (IO.userError "tripled statement")
  let .returnStmt (some tupleId) := statement.form | throw (IO.userError "tripled return")
  let some tuple := source.lookupExpression? tupleId | throw (IO.userError "tripled tuple")
  let .tuple [firstId, secondId, thirdId] := tuple.form | throw (IO.userError "tripled tuple form")
  let some firstNode := source.lookupExpression? firstId | throw (IO.userError "tripled first")
  let some secondNode := source.lookupExpression? secondId | throw (IO.userError "tripled second")
  let some thirdNode := source.lookupExpression? thirdId | throw (IO.userError "tripled third")
  let first ← Tests.SourceCoreNamedBranch.observeRead source binder firstNode .word
  let second ← Tests.SourceCoreNamedBranch.observeRead source binder secondNode .word
  let third ← Tests.SourceCoreNamedBranch.observeRead source binder thirdNode .word
  let ⟨inputs⟩ ← observed (source.inputs = [binder]) "tripled inputs"
  let ⟨roots⟩ ← observed (source.roots = [.statement statement.id]) "tripled roots shape"
  let ⟨statementFound⟩ ← observed (source.lookupStatement? statement.id = some statement) "tripled statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some tuple.id)) "tripled statementForm"
  let ⟨tupleFound⟩ ← observed (source.lookupExpression? tuple.id = some tuple) "tripled tupleFound"
  let ⟨tupleForm⟩ ← observed (tuple.form = .tuple [first.node.id, second.node.id, third.node.id]) "tripled tupleForm"
  let ⟨tupleRaw⟩ ← observed (tuple.rawType = TypeSystem.Ty.productMany [.word, .word, .word]) "tripled tupleRaw"
  let ⟨tupleType⟩ ← observed (tuple.type = TypeSystem.Ty.productMany [.word, .word, .word]) "tripled tupleType"
  let ⟨tupleRequirements⟩ ← observed (tuple.requirements = []) "tripled tupleRequirements"
  let ⟨tupleCoercions⟩ ← observed (tuple.coercions = []) "tripled tupleCoercions"
  return ⟨binder, first, second, third, tuple, statement, inputs, roots, statementFound, statementForm, tupleFound,
    tupleForm, tupleRaw, tupleType, tupleRequirements, tupleCoercions⟩

/-- `tripled`'s body: the return of `(value, value, value)`. -/
structure TripledShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  parts : TripledParts function.typedBody
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [TypeSystem.Ty.productMany [.word, .word, .word]]
  binderRequirements : parts.binder.schemeRequirements = []
  statementType : parts.statement.type = TypeSystem.Ty.productMany [.word, .word, .word]

theorem TripledShape.statementTyping {function : CheckedFunction} {signature : ProgramFunctionSignature}
    (shape : TripledShape function signature) (signatures : ProgramSignatures) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.parts.statement.id] :=
    statementRoots_injective (roots.symm.trans shape.parts.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type := TypeSystem.Ty.productMany [.word, .word, .word], hasValue := true, sawReturn := true, control := .returned}
  refine ⟨BodyFacts.singleton facts, rfl, ?_⟩
  intro lexical extension
  rw [shape.parts.inputs, shape.inputTypes] at extension
  cases extension with
  | cons scheme head tail =>
    cases tail
    have binders : TypeParameterBindersWellFormed lexical := by
      rw [TypeParameterBindersWellFormed, head.context_fields.2.2.1]
      simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
        Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
    have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
    have triple : TypeAdmissible lexical (TypeSystem.Ty.productMany [.word, .word, .word]) :=
      ⟨binders, .product (.builtin .word) (.product (.builtin .word) (.builtin .word))⟩
    have firstTyped := shape.parts.first.typed scheme shape.binderRequirements word head.local_self
      head.local_scheme_requirements_self
    have secondTyped := shape.parts.second.typed scheme shape.binderRequirements word head.local_self
      head.local_scheme_requirements_self
    have thirdTyped := shape.parts.third.typed scheme shape.binderRequirements word head.local_self
      head.local_scheme_requirements_self
    have tupleTyped : ExpressionHasType function.typedBody lexical shape.parts.tuple.id shape.parts.tuple.type := by
      apply ExpressionHasType.ofOrdinary (rawType := TypeSystem.Ty.productMany [.word, .word, .word]) (owned := [])
        (lookupExpression?_sound shape.parts.tupleFound)
      · rw [shape.parts.tupleForm]
        exact .tuple (.cons firstTyped (.cons secondTyped (.cons thirdTyped (.nil _))))
      · exact triple
      · rw [shape.parts.tupleType]
        exact triple
      · intro id member
        cases member
      · rw [shape.parts.tupleCoercions, shape.parts.tupleType]
        exact .nil _
      · rw [shape.parts.tupleRequirements, shape.parts.tupleCoercions]
        rfl
    rw [shape.parts.tupleType] at tupleTyped
    exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.parts.statementFound)
      shape.parts.statementForm tupleTyped shape.statementType)⟩

def observeTripled (function : CheckedFunction) (signature : ProgramFunctionSignature) :
    IO (TripledShape function signature) := do
  let parts ← observeTripledParts function.typedBody
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "tripled parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "tripled inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [TypeSystem.Ty.productMany [.word, .word, .word]]) "tripled returns"
  let ⟨binderRequirements⟩ ← observed (parts.binder.schemeRequirements = []) "tripled binderRequirements"
  let ⟨statementType⟩ ← observed (parts.statement.type = TypeSystem.Ty.productMany [.word, .word, .word]) "tripled statementType"
  return ⟨parts, parameters, inputTypes, returns, binderRequirements, statementType⟩

/-- The nodes of `boxed`'s body: a read of its parameter, the application of
`Item` to it and its return, found by following the statement graph. -/
structure BoxedParts (source : TypedSource) where
  binder : TypedBinder
  read : Tests.SourceCoreNamedBranch.Read source binder .word
  instantiation : DataConstructorInstantiation
  construct : ExpressionNode
  statement : StatementNode
  inputs : source.inputs = [binder]
  roots : source.roots = [.statement statement.id]
  statementFound : source.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some construct.id)
  constructFound : source.lookupExpression? construct.id = some construct
  constructForm : construct.form = .constructor instantiation [read.node.id]
  constructRaw : construct.rawType = instantiation.resultType
  constructType : construct.type = instantiation.resultType
  constructRequirements : construct.requirements = []
  constructCoercions : construct.coercions = []
  substitution : instantiation.parameterSubstitution = []
  payloadTypes : instantiation.payloadTypes = [.word]

def observeBoxedParts (source : TypedSource) : IO (BoxedParts source) := do
  let [binder] := source.inputs | throw (IO.userError "boxed input")
  let [.statement statementId] := source.roots | throw (IO.userError "boxed roots")
  let some statement := source.lookupStatement? statementId | throw (IO.userError "boxed statement")
  let .returnStmt (some constructId) := statement.form | throw (IO.userError "boxed return")
  let some construct := source.lookupExpression? constructId | throw (IO.userError "boxed construct")
  let .constructor instantiation [argumentId] := construct.form | throw (IO.userError "boxed construct form")
  let some argumentNode := source.lookupExpression? argumentId | throw (IO.userError "boxed argument")
  let read ← Tests.SourceCoreNamedBranch.observeRead source binder argumentNode .word
  let ⟨inputs⟩ ← observed (source.inputs = [binder]) "boxed inputs"
  let ⟨roots⟩ ← observed (source.roots = [.statement statement.id]) "boxed roots shape"
  let ⟨statementFound⟩ ← observed (source.lookupStatement? statement.id = some statement) "boxed statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some construct.id)) "boxed statementForm"
  let ⟨constructFound⟩ ← observed (source.lookupExpression? construct.id = some construct) "boxed constructFound"
  let ⟨constructForm⟩ ← observed (construct.form = .constructor instantiation [read.node.id]) "boxed constructForm"
  let ⟨constructRaw⟩ ← observed (construct.rawType = instantiation.resultType) "boxed constructRaw"
  let ⟨constructType⟩ ← observed (construct.type = instantiation.resultType) "boxed constructType"
  let ⟨constructRequirements⟩ ← observed (construct.requirements = []) "boxed constructRequirements"
  let ⟨constructCoercions⟩ ← observed (construct.coercions = []) "boxed constructCoercions"
  let ⟨substitution⟩ ← observed (instantiation.parameterSubstitution = []) "boxed substitution"
  let ⟨payloadTypes⟩ ← observed (instantiation.payloadTypes = [.word]) "boxed payloadTypes"
  return ⟨binder, read, instantiation, construct, statement, inputs, roots, statementFound, statementForm,
    constructFound, constructForm, constructRaw, constructType, constructRequirements, constructCoercions,
    substitution, payloadTypes⟩

/-- `boxed`'s body: the return of `.Item(value)`, with `Box`'s declaration and
`Item`'s signature among the program's data types. -/
structure BoxedShape (function : CheckedFunction) (signature : ProgramFunctionSignature)
    (dataTypes : List ProgramDataSignature) where
  parts : BoxedParts function.typedBody
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [parts.instantiation.resultType]
  binderRequirements : parts.binder.schemeRequirements = []
  statementType : parts.statement.type = parts.instantiation.resultType
  dataType : ProgramDataSignature
  constructorSignature : ProgramDataConstructorSignature
  dataMember : dataType ∈ dataTypes
  constructorMember : constructorSignature ∈ dataType.constructors
  owner : constructorSignature.id.dataType = dataType.id
  constructorEq : parts.instantiation.constructor = constructorSignature.id
  dataParameters : dataType.parameters = []
  payload : parts.instantiation.payloadTypes = constructorSignature.payloadTypes.map
    (TypeSystem.ParameterSubstitution.apply parts.instantiation.parameterSubstitution)
  result : parts.instantiation.resultType = TypeSystem.Ty.nominal dataType.id
    (ParameterSubstitution.orderedArguments parts.instantiation.parameterSubstitution dataType.parameters)

theorem BoxedShape.statementTyping {function : CheckedFunction} {signature : ProgramFunctionSignature}
    {dataTypes : List ProgramDataSignature} (shape : BoxedShape function signature dataTypes)
    (signatures : ProgramSignatures) (dataTypesEq : signatures.dataTypes = dataTypes) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.parts.statement.id] :=
    statementRoots_injective (roots.symm.trans shape.parts.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type := shape.parts.instantiation.resultType, hasValue := true, sawReturn := true, control := .returned}
  refine ⟨BodyFacts.singleton facts, rfl, ?_⟩
  intro lexical extension
  rw [shape.parts.inputs, shape.inputTypes] at extension
  cases extension with
  | cons scheme head tail =>
    cases tail
    have binders : TypeParameterBindersWellFormed lexical := by
      rw [TypeParameterBindersWellFormed, head.context_fields.2.2.1]
      simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
        Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
    have dataMember : shape.dataType ∈ lexical.signatures.dataTypes := by
      rw [head.context_fields.1]
      simpa [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
        Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, dataTypesEq]
        using shape.dataMember
    have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
    have boxType : TypeAdmissible lexical shape.parts.instantiation.resultType := by
      rw [shape.result, shape.parts.substitution, shape.dataParameters]
      exact ⟨binders, .nominal shape.dataType [] dataMember (by simp [shape.dataParameters]) .nil⟩
    have readTyped := shape.parts.read.typed scheme shape.binderRequirements word head.local_self
      head.local_scheme_requirements_self
    have admissible : DataConstructorInstantiation.Admissible lexical shape.parts.instantiation :=
      .intro shape.dataType shape.constructorSignature dataMember shape.constructorMember shape.owner
        shape.constructorEq
        (by rw [shape.parts.substitution, shape.dataParameters]; exact ParameterSubstitution.exact_empty)
        (by rw [shape.parts.substitution]; intro parameter replacement impossible; cases impossible)
        shape.payload shape.result
    have constructTyped : ExpressionHasType function.typedBody lexical shape.parts.construct.id
        shape.parts.construct.type := by
      apply ExpressionHasType.ofOrdinary (rawType := shape.parts.instantiation.resultType) (owned := [])
        (lookupExpression?_sound shape.parts.constructFound)
      · rw [shape.parts.constructForm]
        exact .constructor admissible (by rw [shape.parts.payloadTypes]; exact .cons readTyped (.nil _))
      · exact boxType
      · rw [shape.parts.constructType]
        exact boxType
      · intro id member
        cases member
      · rw [shape.parts.constructCoercions, shape.parts.constructType]
        exact .nil _
      · rw [shape.parts.constructRequirements, shape.parts.constructCoercions]
        rfl
    rw [shape.parts.constructType] at constructTyped
    exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.parts.statementFound)
      shape.parts.statementForm constructTyped shape.statementType)⟩

def observeBoxed (function : CheckedFunction) (signature : ProgramFunctionSignature)
    (dataTypes : List ProgramDataSignature) : IO (BoxedShape function signature dataTypes) := do
  let parts ← observeBoxedParts function.typedBody
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "boxed parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "boxed inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [parts.instantiation.resultType]) "boxed returns"
  let ⟨binderRequirements⟩ ← observed (parts.binder.schemeRequirements = []) "boxed binderRequirements"
  let ⟨statementType⟩ ← observed (parts.statement.type = parts.instantiation.resultType) "boxed statementType"
  match dataFound : dataTypes.find? (fun dataType => dataType.id == parts.instantiation.constructor.dataType) with
  | none => throw (IO.userError "boxed data type")
  | some dataType =>
    match constructorFound : dataType.constructors.find?
        (fun constructor => constructor.id == parts.instantiation.constructor) with
    | none => throw (IO.userError "boxed constructor signature")
    | some constructorSignature =>
      let ⟨owner⟩ ← observed (constructorSignature.id.dataType = dataType.id) "boxed owner"
      let ⟨constructorEq⟩ ← observed (parts.instantiation.constructor = constructorSignature.id) "boxed constructorEq"
      let ⟨dataParameters⟩ ← observed (dataType.parameters = []) "boxed dataParameters"
      let ⟨payload⟩ ← observed (parts.instantiation.payloadTypes = constructorSignature.payloadTypes.map
        (TypeSystem.ParameterSubstitution.apply parts.instantiation.parameterSubstitution)) "boxed payload"
      let ⟨result⟩ ← observed (parts.instantiation.resultType = TypeSystem.Ty.nominal dataType.id
        (ParameterSubstitution.orderedArguments parts.instantiation.parameterSubstitution dataType.parameters))
        "boxed result"
      return ⟨parts, parameters, inputTypes, returns, binderRequirements, statementType, dataType,
        constructorSignature, List.mem_of_find?_eq_some dataFound, List.mem_of_find?_eq_some constructorFound,
        owner, constructorEq, dataParameters, payload, result⟩

/-- The nodes of `filled`'s body: a read of its parameter, its conversion to `uint256`, the new
array of that length, the array's length and its return, found by following the statement graph. -/
structure FilledParts (source : TypedSource) where
  binder : TypedBinder
  statement : StatementNode
  inputs : source.inputs = [binder]
  roots : source.roots = [.statement statement.id]
  statementFound : source.lookupStatement? statement.id = some statement
  read : Tests.SourceCoreNamedBranch.Read source binder .word
  converted : Tests.SourceCoreBuiltinCalls.BuiltinCall source (.fixedFromWord ⟨false, .w256⟩) read.node.id
  created : Tests.SourceCoreOperatorCalls.TypedNode source (TypeSystem.Ty.array .word)
  createdForm : created.node.form = .newArray .word converted.value.node.id
  measured : Tests.SourceCoreOperatorCalls.TypedNode source (.fixed ⟨false, .w256⟩)
  measuredForm : measured.node.form = .arrayLength created.node.id
  statementForm : statement.form = .returnStmt (some measured.node.id)

def observeFilledParts (source : TypedSource) : IO (FilledParts source) := do
  let [binder] := source.inputs | throw (IO.userError "filled input")
  let [.statement statementId] := source.roots | throw (IO.userError "filled roots")
  let some statement := source.lookupStatement? statementId | throw (IO.userError "filled statement")
  let .returnStmt (some measuredId) := statement.form | throw (IO.userError "filled return")
  let some measuredNode := source.lookupExpression? measuredId | throw (IO.userError "filled result")
  let .arrayLength createdId := measuredNode.form | throw (IO.userError "filled length form")
  let some createdNode := source.lookupExpression? createdId | throw (IO.userError "filled new")
  let .newArray _ convertedId := createdNode.form | throw (IO.userError "filled new form")
  let some convertedNode := source.lookupExpression? convertedId | throw (IO.userError "filled conversion")
  let .call calleeId [readId] _ := convertedNode.form | throw (IO.userError "filled conversion form")
  let some calleeNode := source.lookupExpression? calleeId | throw (IO.userError "filled callee")
  let some readNode := source.lookupExpression? readId | throw (IO.userError "filled read")
  let read ← Tests.SourceCoreNamedBranch.observeRead source binder readNode .word
  let converted ← observeConversion source (.fixedFromWord ⟨false, .w256⟩) read.node.id calleeNode convertedNode
  let created ← Tests.SourceCoreOperatorCalls.observeNode source createdNode (TypeSystem.Ty.array .word)
  let ⟨createdForm⟩ ← observed (created.node.form = .newArray .word converted.value.node.id) "filled createdForm"
  let measured ← Tests.SourceCoreOperatorCalls.observeNode source measuredNode (.fixed ⟨false, .w256⟩)
  let ⟨measuredForm⟩ ← observed (measured.node.form = .arrayLength created.node.id) "filled measuredForm"
  let ⟨inputs⟩ ← observed (source.inputs = [binder]) "filled inputs"
  let ⟨roots⟩ ← observed (source.roots = [.statement statement.id]) "filled roots shape"
  let ⟨statementFound⟩ ← observed (source.lookupStatement? statement.id = some statement) "filled statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some measured.node.id)) "filled statementForm"
  return ⟨binder, statement, inputs, roots, statementFound, read, converted, created, createdForm, measured,
    measuredForm, statementForm⟩

/-- `filled`'s body: the return of the length of `new Word[](uint256(value))`. -/
structure FilledShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  parts : FilledParts function.typedBody
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [.fixed ⟨false, .w256⟩]
  binderRequirements : parts.binder.schemeRequirements = []
  statementType : parts.statement.type = .fixed ⟨false, .w256⟩
theorem FilledShape.statementTyping {function : CheckedFunction} {signature : ProgramFunctionSignature}
    (shape : FilledShape function signature) (signatures : ProgramSignatures) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.parts.statement.id] :=
    statementRoots_injective (roots.symm.trans shape.parts.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type := .fixed ⟨false, .w256⟩, hasValue := true, sawReturn := true, control := .returned}
  refine ⟨BodyFacts.singleton facts, rfl, ?_⟩
  intro lexical extension
  rw [shape.parts.inputs, shape.inputTypes] at extension
  cases extension with
  | cons scheme head tail =>
    cases tail
    have binders : TypeParameterBindersWellFormed lexical := by
      rw [TypeParameterBindersWellFormed, head.context_fields.2.2.1]
      simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
        Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
    have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
    have wide : TypeAdmissible lexical (.fixed ⟨false, .w256⟩) := ⟨binders, .builtin (.fixed ⟨false, .w256⟩)⟩
    have array : TypeAdmissible lexical (TypeSystem.Ty.array .word) := ⟨binders, .array (.builtin .word)⟩
    have slice : TypeAdmissible lexical (TypeSystem.Ty.arraySlice (TypeSystem.Ty.array .word)) :=
      ⟨binders, .arraySlice (.array (.builtin .word))⟩
    have read := shape.parts.read.typed scheme shape.binderRequirements word head.local_self
      head.local_scheme_requirements_self
    have converted := shape.parts.converted.typed rfl wide read
    have createdTyped := shape.parts.created.ordinary array (by
      rw [shape.parts.createdForm]
      exact .newArray rfl word converted)
    have measuredTyped := shape.parts.measured.ordinary wide (by
      rw [shape.parts.measuredForm]
      exact .arrayLength createdTyped (.array .word))
    exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.parts.statementFound)
      shape.parts.statementForm measuredTyped shape.statementType)⟩

def observeFilled (function : CheckedFunction) (signature : ProgramFunctionSignature) :
    IO (FilledShape function signature) := do
  let parts ← observeFilledParts function.typedBody
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "filled parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "filled inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.fixed ⟨false, .w256⟩]) "filled returns"
  let ⟨binderRequirements⟩ ← observed (parts.binder.schemeRequirements = []) "filled binderRequirements"
  let ⟨statementType⟩ ← observed (parts.statement.type = .fixed ⟨false, .w256⟩) "filled statementType"
  return ⟨parts, parameters, inputTypes, returns, binderRequirements, statementType⟩

/-- The nodes of `listed`'s body: three reads of its parameter in a literal, a fourth as the index,
the read of the literal there and its return, found by following the statement graph. -/
structure ListedParts (source : TypedSource) where
  binder : TypedBinder
  statement : StatementNode
  inputs : source.inputs = [binder]
  roots : source.roots = [.statement statement.id]
  statementFound : source.lookupStatement? statement.id = some statement
  first : Tests.SourceCoreNamedBranch.Read source binder .word
  second : Tests.SourceCoreNamedBranch.Read source binder .word
  third : Tests.SourceCoreNamedBranch.Read source binder .word
  literal : Tests.SourceCoreOperatorCalls.TypedNode source (TypeSystem.Ty.array .word)
  literalForm : literal.node.form = .arrayLiteral .word [first.node.id, second.node.id, third.node.id]
  index : Tests.SourceCoreNamedBranch.Read source binder .word
  read : Tests.SourceCoreOperatorCalls.TypedNode source .word
  readForm : read.node.form = .arrayIndex literal.node.id index.node.id
  statementForm : statement.form = .returnStmt (some read.node.id)

def observeListedParts (source : TypedSource) : IO (ListedParts source) := do
  let [binder] := source.inputs | throw (IO.userError "listed input")
  let [.statement statementId] := source.roots | throw (IO.userError "listed roots")
  let some statement := source.lookupStatement? statementId | throw (IO.userError "listed statement")
  let .returnStmt (some readId) := statement.form | throw (IO.userError "listed return")
  let some readNode := source.lookupExpression? readId | throw (IO.userError "listed result")
  let .arrayIndex literalId indexId := readNode.form | throw (IO.userError "listed read form")
  let some literalNode := source.lookupExpression? literalId | throw (IO.userError "listed literal")
  let some indexNode := source.lookupExpression? indexId | throw (IO.userError "listed index")
  let .arrayLiteral _ [firstId, secondId, thirdId] := literalNode.form | throw (IO.userError "listed literal form")
  let some firstNode := source.lookupExpression? firstId | throw (IO.userError "listed first")
  let some secondNode := source.lookupExpression? secondId | throw (IO.userError "listed second")
  let some thirdNode := source.lookupExpression? thirdId | throw (IO.userError "listed third")
  let first ← Tests.SourceCoreNamedBranch.observeRead source binder firstNode .word
  let second ← Tests.SourceCoreNamedBranch.observeRead source binder secondNode .word
  let third ← Tests.SourceCoreNamedBranch.observeRead source binder thirdNode .word
  let literal ← Tests.SourceCoreOperatorCalls.observeNode source literalNode (TypeSystem.Ty.array .word)
  let ⟨literalForm⟩ ← observed (literal.node.form = .arrayLiteral .word [first.node.id, second.node.id, third.node.id])
    "listed literalForm"
  let index ← Tests.SourceCoreNamedBranch.observeRead source binder indexNode .word
  let read ← Tests.SourceCoreOperatorCalls.observeNode source readNode .word
  let ⟨readForm⟩ ← observed (read.node.form = .arrayIndex literal.node.id index.node.id) "listed readForm"
  let ⟨inputs⟩ ← observed (source.inputs = [binder]) "listed inputs"
  let ⟨roots⟩ ← observed (source.roots = [.statement statement.id]) "listed roots shape"
  let ⟨statementFound⟩ ← observed (source.lookupStatement? statement.id = some statement) "listed statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some read.node.id)) "listed statementForm"
  return ⟨binder, statement, inputs, roots, statementFound, first, second, third, literal, literalForm, index, read,
    readForm, statementForm⟩

/-- `listed`'s body: the return of `[value, value, value][value]`. -/
structure ListedShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  parts : ListedParts function.typedBody
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [.word]
  binderRequirements : parts.binder.schemeRequirements = []
  statementType : parts.statement.type = .word
theorem ListedShape.statementTyping {function : CheckedFunction} {signature : ProgramFunctionSignature}
    (shape : ListedShape function signature) (signatures : ProgramSignatures) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.parts.statement.id] :=
    statementRoots_injective (roots.symm.trans shape.parts.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type := .word, hasValue := true, sawReturn := true, control := .returned}
  refine ⟨BodyFacts.singleton facts, rfl, ?_⟩
  intro lexical extension
  rw [shape.parts.inputs, shape.inputTypes] at extension
  cases extension with
  | cons scheme head tail =>
    cases tail
    have binders : TypeParameterBindersWellFormed lexical := by
      rw [TypeParameterBindersWellFormed, head.context_fields.2.2.1]
      simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
        Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
    have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
    have wide : TypeAdmissible lexical (.fixed ⟨false, .w256⟩) := ⟨binders, .builtin (.fixed ⟨false, .w256⟩)⟩
    have array : TypeAdmissible lexical (TypeSystem.Ty.array .word) := ⟨binders, .array (.builtin .word)⟩
    have slice : TypeAdmissible lexical (TypeSystem.Ty.arraySlice (TypeSystem.Ty.array .word)) :=
      ⟨binders, .arraySlice (.array (.builtin .word))⟩
    have literalTyped := shape.parts.literal.ordinary array (by
      rw [shape.parts.literalForm]
      exact .arrayLiteral word
        (.cons (shape.parts.first.typed scheme shape.binderRequirements word head.local_self
            head.local_scheme_requirements_self)
          (.cons (shape.parts.second.typed scheme shape.binderRequirements word head.local_self
              head.local_scheme_requirements_self)
            (.cons (shape.parts.third.typed scheme shape.binderRequirements word head.local_self
                head.local_scheme_requirements_self) (.nil _)))))
    have indexTyped := shape.parts.index.typed scheme shape.binderRequirements word head.local_self
      head.local_scheme_requirements_self
    have readTyped := shape.parts.read.ordinary word (by
      rw [shape.parts.readForm]
      exact .arrayIndex literalTyped (.array .word) indexTyped .word)
    exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.parts.statementFound)
      shape.parts.statementForm readTyped shape.statementType)⟩

def observeListed (function : CheckedFunction) (signature : ProgramFunctionSignature) :
    IO (ListedShape function signature) := do
  let parts ← observeListedParts function.typedBody
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "listed parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "listed inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.word]) "listed returns"
  let ⟨binderRequirements⟩ ← observed (parts.binder.schemeRequirements = []) "listed binderRequirements"
  let ⟨statementType⟩ ← observed (parts.statement.type = .word) "listed statementType"
  return ⟨parts, parameters, inputTypes, returns, binderRequirements, statementType⟩

/-- The nodes of `sliced`'s body: three reads of its parameter in a literal, a fourth converted to
`uint256` as the slice's start, a fifth as the index, the read through the slice there and its return,
found by following the statement graph. -/
structure SlicedParts (source : TypedSource) where
  binder : TypedBinder
  statement : StatementNode
  inputs : source.inputs = [binder]
  roots : source.roots = [.statement statement.id]
  statementFound : source.lookupStatement? statement.id = some statement
  first : Tests.SourceCoreNamedBranch.Read source binder .word
  second : Tests.SourceCoreNamedBranch.Read source binder .word
  third : Tests.SourceCoreNamedBranch.Read source binder .word
  literal : Tests.SourceCoreOperatorCalls.TypedNode source (TypeSystem.Ty.array .word)
  literalForm : literal.node.form = .arrayLiteral .word [first.node.id, second.node.id, third.node.id]
  bound : Tests.SourceCoreNamedBranch.Read source binder .word
  converted : Tests.SourceCoreBuiltinCalls.BuiltinCall source (.fixedFromWord ⟨false, .w256⟩) bound.node.id
  slice : Tests.SourceCoreOperatorCalls.TypedNode source (TypeSystem.Ty.arraySlice (TypeSystem.Ty.array .word))
  sliceForm : slice.node.form = .arraySlice literal.node.id (some converted.value.node.id) none
  index : Tests.SourceCoreNamedBranch.Read source binder .word
  read : Tests.SourceCoreOperatorCalls.TypedNode source .word
  readForm : read.node.form = .arrayIndex slice.node.id index.node.id
  statementForm : statement.form = .returnStmt (some read.node.id)

def observeSlicedParts (source : TypedSource) : IO (SlicedParts source) := do
  let [binder] := source.inputs | throw (IO.userError "sliced input")
  let [.statement statementId] := source.roots | throw (IO.userError "sliced roots")
  let some statement := source.lookupStatement? statementId | throw (IO.userError "sliced statement")
  let .returnStmt (some readId) := statement.form | throw (IO.userError "sliced return")
  let some readNode := source.lookupExpression? readId | throw (IO.userError "sliced result")
  let .arrayIndex sliceId indexId := readNode.form | throw (IO.userError "sliced read form")
  let some sliceNode := source.lookupExpression? sliceId | throw (IO.userError "sliced slice")
  let some indexNode := source.lookupExpression? indexId | throw (IO.userError "sliced index")
  let .arraySlice literalId (some convertedId) none := sliceNode.form | throw (IO.userError "sliced slice form")
  let some literalNode := source.lookupExpression? literalId | throw (IO.userError "sliced literal")
  let some convertedNode := source.lookupExpression? convertedId | throw (IO.userError "sliced conversion")
  let .call calleeId [boundId] _ := convertedNode.form | throw (IO.userError "sliced conversion form")
  let some calleeNode := source.lookupExpression? calleeId | throw (IO.userError "sliced callee")
  let some boundNode := source.lookupExpression? boundId | throw (IO.userError "sliced bound")
  let .arrayLiteral _ [firstId, secondId, thirdId] := literalNode.form | throw (IO.userError "sliced literal form")
  let some firstNode := source.lookupExpression? firstId | throw (IO.userError "sliced first")
  let some secondNode := source.lookupExpression? secondId | throw (IO.userError "sliced second")
  let some thirdNode := source.lookupExpression? thirdId | throw (IO.userError "sliced third")
  let first ← Tests.SourceCoreNamedBranch.observeRead source binder firstNode .word
  let second ← Tests.SourceCoreNamedBranch.observeRead source binder secondNode .word
  let third ← Tests.SourceCoreNamedBranch.observeRead source binder thirdNode .word
  let literal ← Tests.SourceCoreOperatorCalls.observeNode source literalNode (TypeSystem.Ty.array .word)
  let ⟨literalForm⟩ ← observed (literal.node.form = .arrayLiteral .word [first.node.id, second.node.id, third.node.id])
    "sliced literalForm"
  let bound ← Tests.SourceCoreNamedBranch.observeRead source binder boundNode .word
  let converted ← observeConversion source (.fixedFromWord ⟨false, .w256⟩) bound.node.id calleeNode convertedNode
  let slice ← Tests.SourceCoreOperatorCalls.observeNode source sliceNode
    (TypeSystem.Ty.arraySlice (TypeSystem.Ty.array .word))
  let ⟨sliceForm⟩ ← observed (slice.node.form = .arraySlice literal.node.id (some converted.value.node.id) none)
    "sliced sliceForm"
  let index ← Tests.SourceCoreNamedBranch.observeRead source binder indexNode .word
  let read ← Tests.SourceCoreOperatorCalls.observeNode source readNode .word
  let ⟨readForm⟩ ← observed (read.node.form = .arrayIndex slice.node.id index.node.id) "sliced readForm"
  let ⟨inputs⟩ ← observed (source.inputs = [binder]) "sliced inputs"
  let ⟨roots⟩ ← observed (source.roots = [.statement statement.id]) "sliced roots shape"
  let ⟨statementFound⟩ ← observed (source.lookupStatement? statement.id = some statement) "sliced statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some read.node.id)) "sliced statementForm"
  return ⟨binder, statement, inputs, roots, statementFound, first, second, third, literal, literalForm, bound,
    converted, slice, sliceForm, index, read, readForm, statementForm⟩

/-- `sliced`'s body: the return of `[value, value, value][uint256(value):][value]`. -/
structure SlicedShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  parts : SlicedParts function.typedBody
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [.word]
  binderRequirements : parts.binder.schemeRequirements = []
  statementType : parts.statement.type = .word
theorem SlicedShape.statementTyping {function : CheckedFunction} {signature : ProgramFunctionSignature}
    (shape : SlicedShape function signature) (signatures : ProgramSignatures) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.parts.statement.id] :=
    statementRoots_injective (roots.symm.trans shape.parts.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type := .word, hasValue := true, sawReturn := true, control := .returned}
  refine ⟨BodyFacts.singleton facts, rfl, ?_⟩
  intro lexical extension
  rw [shape.parts.inputs, shape.inputTypes] at extension
  cases extension with
  | cons scheme head tail =>
    cases tail
    have binders : TypeParameterBindersWellFormed lexical := by
      rw [TypeParameterBindersWellFormed, head.context_fields.2.2.1]
      simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
        Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
    have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
    have wide : TypeAdmissible lexical (.fixed ⟨false, .w256⟩) := ⟨binders, .builtin (.fixed ⟨false, .w256⟩)⟩
    have array : TypeAdmissible lexical (TypeSystem.Ty.array .word) := ⟨binders, .array (.builtin .word)⟩
    have slice : TypeAdmissible lexical (TypeSystem.Ty.arraySlice (TypeSystem.Ty.array .word)) :=
      ⟨binders, .arraySlice (.array (.builtin .word))⟩
    have literalTyped := shape.parts.literal.ordinary array (by
      rw [shape.parts.literalForm]
      exact .arrayLiteral word
        (.cons (shape.parts.first.typed scheme shape.binderRequirements word head.local_self
            head.local_scheme_requirements_self)
          (.cons (shape.parts.second.typed scheme shape.binderRequirements word head.local_self
              head.local_scheme_requirements_self)
            (.cons (shape.parts.third.typed scheme shape.binderRequirements word head.local_self
                head.local_scheme_requirements_self) (.nil _)))))
    have boundTyped := shape.parts.bound.typed scheme shape.binderRequirements word head.local_self
      head.local_scheme_requirements_self
    have converted := shape.parts.converted.typed rfl wide boundTyped
    have sliceTyped := shape.parts.slice.ordinary slice (by
      rw [shape.parts.sliceForm]
      exact .arraySlice rfl literalTyped (.cons converted (.nil _)))
    have indexTyped := shape.parts.index.typed scheme shape.binderRequirements word head.local_self
      head.local_scheme_requirements_self
    have readTyped := shape.parts.read.ordinary word (by
      rw [shape.parts.readForm]
      exact .arrayIndex sliceTyped (.slice (.array .word)) indexTyped .word)
    exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.parts.statementFound)
      shape.parts.statementForm readTyped shape.statementType)⟩

def observeSliced (function : CheckedFunction) (signature : ProgramFunctionSignature) :
    IO (SlicedShape function signature) := do
  let parts ← observeSlicedParts function.typedBody
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "sliced parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "sliced inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.word]) "sliced returns"
  let ⟨binderRequirements⟩ ← observed (parts.binder.schemeRequirements = []) "sliced binderRequirements"
  let ⟨statementType⟩ ← observed (parts.statement.type = .word) "sliced statementType"
  return ⟨parts, parameters, inputTypes, returns, binderRequirements, statementType⟩

/-- The nodes of `copied`'s body: three reads of its parameter in a literal, its whole slice, the
slice's copy, a fourth read as the index, the read of the copy there and its return, found by following
the statement graph. -/
structure CopiedParts (source : TypedSource) where
  binder : TypedBinder
  statement : StatementNode
  inputs : source.inputs = [binder]
  roots : source.roots = [.statement statement.id]
  statementFound : source.lookupStatement? statement.id = some statement
  first : Tests.SourceCoreNamedBranch.Read source binder .word
  second : Tests.SourceCoreNamedBranch.Read source binder .word
  third : Tests.SourceCoreNamedBranch.Read source binder .word
  literal : Tests.SourceCoreOperatorCalls.TypedNode source (TypeSystem.Ty.array .word)
  literalForm : literal.node.form = .arrayLiteral .word [first.node.id, second.node.id, third.node.id]
  slice : Tests.SourceCoreOperatorCalls.TypedNode source (TypeSystem.Ty.arraySlice (TypeSystem.Ty.array .word))
  sliceForm : slice.node.form = .arraySlice literal.node.id none none
  copy : Tests.SourceCoreOperatorCalls.TypedNode source (TypeSystem.Ty.array .word)
  copyForm : copy.node.form = .toArray .word slice.node.id
  index : Tests.SourceCoreNamedBranch.Read source binder .word
  read : Tests.SourceCoreOperatorCalls.TypedNode source .word
  readForm : read.node.form = .arrayIndex copy.node.id index.node.id
  statementForm : statement.form = .returnStmt (some read.node.id)

def observeCopiedParts (source : TypedSource) : IO (CopiedParts source) := do
  let [binder] := source.inputs | throw (IO.userError "copied input")
  let [.statement statementId] := source.roots | throw (IO.userError "copied roots")
  let some statement := source.lookupStatement? statementId | throw (IO.userError "copied statement")
  let .returnStmt (some readId) := statement.form | throw (IO.userError "copied return")
  let some readNode := source.lookupExpression? readId | throw (IO.userError "copied result")
  let .arrayIndex copyId indexId := readNode.form | throw (IO.userError "copied read form")
  let some copyNode := source.lookupExpression? copyId | throw (IO.userError "copied copy")
  let some indexNode := source.lookupExpression? indexId | throw (IO.userError "copied index")
  let .toArray _ sliceId := copyNode.form | throw (IO.userError "copied copy form")
  let some sliceNode := source.lookupExpression? sliceId | throw (IO.userError "copied slice")
  let .arraySlice literalId none none := sliceNode.form | throw (IO.userError "copied slice form")
  let some literalNode := source.lookupExpression? literalId | throw (IO.userError "copied literal")
  let .arrayLiteral _ [firstId, secondId, thirdId] := literalNode.form | throw (IO.userError "copied literal form")
  let some firstNode := source.lookupExpression? firstId | throw (IO.userError "copied first")
  let some secondNode := source.lookupExpression? secondId | throw (IO.userError "copied second")
  let some thirdNode := source.lookupExpression? thirdId | throw (IO.userError "copied third")
  let first ← Tests.SourceCoreNamedBranch.observeRead source binder firstNode .word
  let second ← Tests.SourceCoreNamedBranch.observeRead source binder secondNode .word
  let third ← Tests.SourceCoreNamedBranch.observeRead source binder thirdNode .word
  let literal ← Tests.SourceCoreOperatorCalls.observeNode source literalNode (TypeSystem.Ty.array .word)
  let ⟨literalForm⟩ ← observed (literal.node.form = .arrayLiteral .word [first.node.id, second.node.id, third.node.id])
    "copied literalForm"
  let slice ← Tests.SourceCoreOperatorCalls.observeNode source sliceNode
    (TypeSystem.Ty.arraySlice (TypeSystem.Ty.array .word))
  let ⟨sliceForm⟩ ← observed (slice.node.form = .arraySlice literal.node.id none none) "copied sliceForm"
  let copy ← Tests.SourceCoreOperatorCalls.observeNode source copyNode (TypeSystem.Ty.array .word)
  let ⟨copyForm⟩ ← observed (copy.node.form = .toArray .word slice.node.id) "copied copyForm"
  let index ← Tests.SourceCoreNamedBranch.observeRead source binder indexNode .word
  let read ← Tests.SourceCoreOperatorCalls.observeNode source readNode .word
  let ⟨readForm⟩ ← observed (read.node.form = .arrayIndex copy.node.id index.node.id) "copied readForm"
  let ⟨inputs⟩ ← observed (source.inputs = [binder]) "copied inputs"
  let ⟨roots⟩ ← observed (source.roots = [.statement statement.id]) "copied roots shape"
  let ⟨statementFound⟩ ← observed (source.lookupStatement? statement.id = some statement) "copied statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some read.node.id)) "copied statementForm"
  return ⟨binder, statement, inputs, roots, statementFound, first, second, third, literal, literalForm, slice,
    sliceForm, copy, copyForm, index, read, readForm, statementForm⟩

/-- `copied`'s body: the return of `toArray([value, value, value][:])[value]`. -/
structure CopiedShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  parts : CopiedParts function.typedBody
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [.word]
  binderRequirements : parts.binder.schemeRequirements = []
  statementType : parts.statement.type = .word
theorem CopiedShape.statementTyping {function : CheckedFunction} {signature : ProgramFunctionSignature}
    (shape : CopiedShape function signature) (signatures : ProgramSignatures) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.parts.statement.id] :=
    statementRoots_injective (roots.symm.trans shape.parts.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type := .word, hasValue := true, sawReturn := true, control := .returned}
  refine ⟨BodyFacts.singleton facts, rfl, ?_⟩
  intro lexical extension
  rw [shape.parts.inputs, shape.inputTypes] at extension
  cases extension with
  | cons scheme head tail =>
    cases tail
    have binders : TypeParameterBindersWellFormed lexical := by
      rw [TypeParameterBindersWellFormed, head.context_fields.2.2.1]
      simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
        Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
    have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
    have wide : TypeAdmissible lexical (.fixed ⟨false, .w256⟩) := ⟨binders, .builtin (.fixed ⟨false, .w256⟩)⟩
    have array : TypeAdmissible lexical (TypeSystem.Ty.array .word) := ⟨binders, .array (.builtin .word)⟩
    have slice : TypeAdmissible lexical (TypeSystem.Ty.arraySlice (TypeSystem.Ty.array .word)) :=
      ⟨binders, .arraySlice (.array (.builtin .word))⟩
    have literalTyped := shape.parts.literal.ordinary array (by
      rw [shape.parts.literalForm]
      exact .arrayLiteral word
        (.cons (shape.parts.first.typed scheme shape.binderRequirements word head.local_self
            head.local_scheme_requirements_self)
          (.cons (shape.parts.second.typed scheme shape.binderRequirements word head.local_self
              head.local_scheme_requirements_self)
            (.cons (shape.parts.third.typed scheme shape.binderRequirements word head.local_self
                head.local_scheme_requirements_self) (.nil _)))))
    have sliceTyped := shape.parts.slice.ordinary slice (by
      rw [shape.parts.sliceForm]
      exact .arraySlice rfl literalTyped (.nil _))
    have copyTyped := shape.parts.copy.ordinary array (by
      rw [shape.parts.copyForm]
      exact .toArray sliceTyped (.array .word))
    have indexTyped := shape.parts.index.typed scheme shape.binderRequirements word head.local_self
      head.local_scheme_requirements_self
    have readTyped := shape.parts.read.ordinary word (by
      rw [shape.parts.readForm]
      exact .arrayIndex copyTyped (.array .word) indexTyped .word)
    exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.parts.statementFound)
      shape.parts.statementForm readTyped shape.statementType)⟩

def observeCopied (function : CheckedFunction) (signature : ProgramFunctionSignature) :
    IO (CopiedShape function signature) := do
  let parts ← observeCopiedParts function.typedBody
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "copied parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "copied inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.word]) "copied returns"
  let ⟨binderRequirements⟩ ← observed (parts.binder.schemeRequirements = []) "copied binderRequirements"
  let ⟨statementType⟩ ← observed (parts.statement.type = .word) "copied statementType"
  return ⟨parts, parameters, inputTypes, returns, binderRequirements, statementType⟩

/-- The nodes of `referenced`'s body: its local `a` initialized by a literal of three reads of its
parameter, `CanStore.store(lidx(a, value), value)` and the return of `CanStore.load(lidx(a, value))`, found
by following the statement graph. -/
structure ReferencedParts (source : TypedSource) where
  binder : TypedBinder
  target : TypedBinder
  initialized : StatementNode
  stored : StatementNode
  returned : StatementNode
  inputs : source.inputs = [binder]
  roots : source.roots = [.statement initialized.id, .statement stored.id, .statement returned.id]
  initializedFound : source.lookupStatement? initialized.id = some initialized
  storedFound : source.lookupStatement? stored.id = some stored
  returnedFound : source.lookupStatement? returned.id = some returned
  first : Tests.SourceCoreNamedBranch.Read source binder .word
  second : Tests.SourceCoreNamedBranch.Read source binder .word
  third : Tests.SourceCoreNamedBranch.Read source binder .word
  literal : Tests.SourceCoreOperatorCalls.TypedNode source (TypeSystem.Ty.array .word)
  literalForm : literal.node.form = .arrayLiteral .word [first.node.id, second.node.id, third.node.id]
  initializedForm : initialized.form = .letDecl target (some literal.node.id)
  storeArray : Tests.SourceCoreNamedBranch.Read source target (TypeSystem.Ty.array .word)
  storeIndex : Tests.SourceCoreNamedBranch.Read source binder .word
  storeReference : Tests.SourceCoreOperatorCalls.TypedNode source (TypeSystem.Ty.memref .word)
  storeReferenceForm : storeReference.node.form = .elementRef storeArray.node.id storeIndex.node.id
  storeValue : Tests.SourceCoreNamedBranch.Read source binder .word
  store : Tests.SourceCoreOperatorCalls.TypedNode source .unit
  storeForm : store.node.form = .memrefStore storeReference.node.id storeValue.node.id
  storedForm : stored.form = .expression store.node.id true
  loadArray : Tests.SourceCoreNamedBranch.Read source target (TypeSystem.Ty.array .word)
  loadIndex : Tests.SourceCoreNamedBranch.Read source binder .word
  loadReference : Tests.SourceCoreOperatorCalls.TypedNode source (TypeSystem.Ty.memref .word)
  loadReferenceForm : loadReference.node.form = .elementRef loadArray.node.id loadIndex.node.id
  load : Tests.SourceCoreOperatorCalls.TypedNode source .word
  loadForm : load.node.form = .memrefLoad loadReference.node.id
  returnedForm : returned.form = .returnStmt (some load.node.id)

def observeReferencedParts (source : TypedSource) : IO (ReferencedParts source) := do
  let [binder] := source.inputs | throw (IO.userError "referenced input")
  let [.statement initializedId, .statement storedId, .statement returnedId] := source.roots
    | throw (IO.userError "referenced roots")
  let some initialized := source.lookupStatement? initializedId | throw (IO.userError "referenced let")
  let some stored := source.lookupStatement? storedId | throw (IO.userError "referenced store statement")
  let some returned := source.lookupStatement? returnedId | throw (IO.userError "referenced return")
  let .letDecl target (some literalId) := initialized.form | throw (IO.userError "referenced let form")
  let .expression storeId true := stored.form | throw (IO.userError "referenced store statement form")
  let .returnStmt (some loadId) := returned.form | throw (IO.userError "referenced return form")
  let some literalNode := source.lookupExpression? literalId | throw (IO.userError "referenced literal")
  let .arrayLiteral _ [firstId, secondId, thirdId] := literalNode.form
    | throw (IO.userError "referenced literal form")
  let some firstNode := source.lookupExpression? firstId | throw (IO.userError "referenced first")
  let some secondNode := source.lookupExpression? secondId | throw (IO.userError "referenced second")
  let some thirdNode := source.lookupExpression? thirdId | throw (IO.userError "referenced third")
  let some storeNode := source.lookupExpression? storeId | throw (IO.userError "referenced store")
  let .memrefStore storeReferenceId storeValueId := storeNode.form | throw (IO.userError "referenced store form")
  let some storeReferenceNode := source.lookupExpression? storeReferenceId
    | throw (IO.userError "referenced store memref")
  let .elementRef storeArrayId storeIndexId := storeReferenceNode.form
    | throw (IO.userError "referenced store memref form")
  let some storeArrayNode := source.lookupExpression? storeArrayId | throw (IO.userError "referenced store array")
  let some storeIndexNode := source.lookupExpression? storeIndexId | throw (IO.userError "referenced store index")
  let some storeValueNode := source.lookupExpression? storeValueId | throw (IO.userError "referenced store value")
  let some loadNode := source.lookupExpression? loadId | throw (IO.userError "referenced load")
  let .memrefLoad loadReferenceId := loadNode.form | throw (IO.userError "referenced load form")
  let some loadReferenceNode := source.lookupExpression? loadReferenceId
    | throw (IO.userError "referenced load memref")
  let .elementRef loadArrayId loadIndexId := loadReferenceNode.form
    | throw (IO.userError "referenced load memref form")
  let some loadArrayNode := source.lookupExpression? loadArrayId | throw (IO.userError "referenced load array")
  let some loadIndexNode := source.lookupExpression? loadIndexId | throw (IO.userError "referenced load index")
  let first ← Tests.SourceCoreNamedBranch.observeRead source binder firstNode .word
  let second ← Tests.SourceCoreNamedBranch.observeRead source binder secondNode .word
  let third ← Tests.SourceCoreNamedBranch.observeRead source binder thirdNode .word
  let literal ← Tests.SourceCoreOperatorCalls.observeNode source literalNode (TypeSystem.Ty.array .word)
  let ⟨literalForm⟩ ← observed (literal.node.form = .arrayLiteral .word [first.node.id, second.node.id, third.node.id])
    "referenced literalForm"
  let storeArray ← Tests.SourceCoreNamedBranch.observeRead source target storeArrayNode (TypeSystem.Ty.array .word)
  let storeIndex ← Tests.SourceCoreNamedBranch.observeRead source binder storeIndexNode .word
  let storeReference ← Tests.SourceCoreOperatorCalls.observeNode source storeReferenceNode
    (TypeSystem.Ty.memref .word)
  let ⟨storeReferenceForm⟩ ← observed
    (storeReference.node.form = .elementRef storeArray.node.id storeIndex.node.id) "referenced storeReferenceForm"
  let storeValue ← Tests.SourceCoreNamedBranch.observeRead source binder storeValueNode .word
  let store ← Tests.SourceCoreOperatorCalls.observeNode source storeNode .unit
  let ⟨storeForm⟩ ← observed (store.node.form = .memrefStore storeReference.node.id storeValue.node.id)
    "referenced storeForm"
  let loadArray ← Tests.SourceCoreNamedBranch.observeRead source target loadArrayNode (TypeSystem.Ty.array .word)
  let loadIndex ← Tests.SourceCoreNamedBranch.observeRead source binder loadIndexNode .word
  let loadReference ← Tests.SourceCoreOperatorCalls.observeNode source loadReferenceNode
    (TypeSystem.Ty.memref .word)
  let ⟨loadReferenceForm⟩ ← observed
    (loadReference.node.form = .elementRef loadArray.node.id loadIndex.node.id) "referenced loadReferenceForm"
  let load ← Tests.SourceCoreOperatorCalls.observeNode source loadNode .word
  let ⟨loadForm⟩ ← observed (load.node.form = .memrefLoad loadReference.node.id) "referenced loadForm"
  let ⟨inputs⟩ ← observed (source.inputs = [binder]) "referenced inputs"
  let ⟨roots⟩ ← observed (source.roots = [.statement initialized.id, .statement stored.id, .statement returned.id])
    "referenced roots shape"
  let ⟨initializedFound⟩ ← observed (source.lookupStatement? initialized.id = some initialized)
    "referenced initializedFound"
  let ⟨storedFound⟩ ← observed (source.lookupStatement? stored.id = some stored) "referenced storedFound"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "referenced returnedFound"
  let ⟨initializedForm⟩ ← observed (initialized.form = .letDecl target (some literal.node.id))
    "referenced initializedForm"
  let ⟨storedForm⟩ ← observed (stored.form = .expression store.node.id true) "referenced storedForm"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some load.node.id)) "referenced returnedForm"
  return ⟨binder, target, initialized, stored, returned, inputs, roots, initializedFound, storedFound,
    returnedFound, first, second, third, literal, literalForm, initializedForm, storeArray, storeIndex,
    storeReference, storeReferenceForm, storeValue, store, storeForm, storedForm, loadArray, loadIndex,
    loadReference, loadReferenceForm, load, loadForm, returnedForm⟩

/-- `referenced`'s body: `let a: Word[] = [value, value, value]`, `CanStore.store(lidx(a, value), value)` and
the return of `CanStore.load(lidx(a, value))`. -/
structure ReferencedShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  parts : ReferencedParts function.typedBody
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [.word]
  binderRequirements : parts.binder.schemeRequirements = []
  targetScheme : parts.target.scheme = .mono (TypeSystem.Ty.array .word)
  targetRequirements : parts.target.schemeRequirements = []
  targetOwner : parts.target.id.owner = function.typedBody.owner
  targetDistinct : parts.target.id ≠ parts.binder.id
  initializedType : parts.initialized.type = .unit
  storedType : parts.stored.type = .unit
  returnedType : parts.returned.type = .word

theorem ReferencedShape.statementTyping {function : CheckedFunction} {signature : ProgramFunctionSignature}
    (shape : ReferencedShape function signature) (signatures : ProgramSignatures) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.parts.initialized.id, shape.parts.stored.id, shape.parts.returned.id] :=
    statementRoots_injective (roots.symm.trans shape.parts.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type := .word, hasValue := true, sawReturn := true, control := .returned}
  let ordinary : StatementFacts := {type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit}
  refine ⟨BodyFacts.cons ordinary (BodyFacts.cons ordinary (BodyFacts.singleton facts)), rfl, ?_⟩
  intro lexical extension
  rw [shape.parts.inputs, shape.inputTypes] at extension
  cases extension with
  | cons scheme head tail =>
    cases tail
    have binders : TypeParameterBindersWellFormed lexical := by
      rw [TypeParameterBindersWellFormed, head.context_fields.2.2.1]
      simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
        Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
    have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
    have array : TypeAdmissible lexical (TypeSystem.Ty.array .word) := ⟨binders, .array (.builtin .word)⟩
    have literalTyped := shape.parts.literal.ordinary array (by
      rw [shape.parts.literalForm]
      exact .arrayLiteral word
        (.cons (shape.parts.first.typed scheme shape.binderRequirements word head.local_self
            head.local_scheme_requirements_self)
          (.cons (shape.parts.second.typed scheme shape.binderRequirements word head.local_self
              head.local_scheme_requirements_self)
            (.cons (shape.parts.third.typed scheme shape.binderRequirements word head.local_self
                head.local_scheme_requirements_self) (.nil _)))))
    let locals := lexical.withLocal shape.parts.target.id shape.parts.target.scheme shape.parts.target.schemeRequirements
    have targetExtended : BinderExtends function.typedBody.owner lexical shape.parts.target locals := by
      apply BinderExtends.intro
      · exact {
          owned := shape.targetOwner
          scheme := shape.targetScheme.symm ▸ SchemeWellFormed.monoAdmissible array
          quantified_fresh := by rw [shape.targetScheme]; simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]
          monomorphic_requirements_empty := fun _ => shape.targetRequirements }
      · cases head
        simp [LocalFresh, Context.withLocal, checkedBodyContext, declarationContext,
          Context.ofSignatures, Context.forDeclaration, Context.withAssumptions,
          Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.targetDistinct]
    have initializedTyped : StatementHasType function.typedBody ⟨.word, 0⟩ lexical
        shape.parts.initialized.id locals ordinary := by
      apply StatementHasType.letInitialized (lookupStatement?_sound shape.parts.initializedFound)
        shape.parts.initializedForm
      · simpa only [shape.targetScheme, TypeSystem.Scheme.mono] using literalTyped
      · rw [shape.targetScheme]; rfl
      · rw [shape.targetScheme]; rfl
      · exact targetExtended
      · exact shape.initializedType
    have localWord : TypeAdmissible locals .word := ⟨binders, .builtin .word⟩
    have localUnit : TypeAdmissible locals .unit := ⟨binders, .builtin .unit⟩
    have localArray : TypeAdmissible locals (TypeSystem.Ty.array .word) := ⟨binders, .array (.builtin .word)⟩
    have localMemref : TypeAdmissible locals (TypeSystem.Ty.memref .word) := ⟨binders, .memref (.builtin .word)⟩
    have parameterLookup : locals.LocalLookup shape.parts.binder.id shape.parts.binder.scheme :=
      .tail shape.targetDistinct head.local_self
    have parameterRequirements :
        locals.LocalSchemeRequirementsLookup shape.parts.binder.id shape.parts.binder.schemeRequirements :=
      .tail shape.targetDistinct head.local_scheme_requirements_self
    have storeArrayTyped := shape.parts.storeArray.typed shape.targetScheme shape.targetRequirements localArray
      targetExtended.local_self targetExtended.local_scheme_requirements_self
    have storeIndexTyped := shape.parts.storeIndex.typed scheme shape.binderRequirements localWord parameterLookup
      parameterRequirements
    have storeReferenceTyped := shape.parts.storeReference.ordinary localMemref (by
      rw [shape.parts.storeReferenceForm]
      exact .elementRef storeArrayTyped storeIndexTyped .word)
    have storeValueTyped := shape.parts.storeValue.typed scheme shape.binderRequirements localWord parameterLookup
      parameterRequirements
    have storeTyped := shape.parts.store.ordinary localUnit (by
      rw [shape.parts.storeForm]
      exact .memrefStore storeReferenceTyped storeValueTyped)
    have storedTyped : StatementHasType function.typedBody ⟨.word, 0⟩ locals shape.parts.stored.id locals ordinary :=
      .expressionDiscard (lookupStatement?_sound shape.parts.storedFound) shape.parts.storedForm storeTyped
        shape.storedType
    have loadArrayTyped := shape.parts.loadArray.typed shape.targetScheme shape.targetRequirements localArray
      targetExtended.local_self targetExtended.local_scheme_requirements_self
    have loadIndexTyped := shape.parts.loadIndex.typed scheme shape.binderRequirements localWord parameterLookup
      parameterRequirements
    have loadReferenceTyped := shape.parts.loadReference.ordinary localMemref (by
      rw [shape.parts.loadReferenceForm]
      exact .elementRef loadArrayTyped loadIndexTyped .word)
    have loadTyped := shape.parts.load.ordinary localWord (by
      rw [shape.parts.loadForm]
      exact .memrefLoad loadReferenceTyped)
    exact ⟨_, .cons initializedTyped (.cons storedTyped (.singleton (.returnValue
      (lookupStatement?_sound shape.parts.returnedFound) shape.parts.returnedForm loadTyped shape.returnedType)))⟩

def observeReferenced (function : CheckedFunction) (signature : ProgramFunctionSignature) :
    IO (ReferencedShape function signature) := do
  let parts ← observeReferencedParts function.typedBody
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "referenced parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "referenced inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.word]) "referenced returns"
  let ⟨binderRequirements⟩ ← observed (parts.binder.schemeRequirements = []) "referenced binderRequirements"
  let ⟨targetScheme⟩ ← observed (parts.target.scheme = .mono (TypeSystem.Ty.array .word)) "referenced targetScheme"
  let ⟨targetRequirements⟩ ← observed (parts.target.schemeRequirements = []) "referenced targetRequirements"
  let ⟨targetOwner⟩ ← observed (parts.target.id.owner = function.typedBody.owner) "referenced targetOwner"
  let ⟨targetDistinct⟩ ← observed (parts.target.id ≠ parts.binder.id) "referenced targetDistinct"
  let ⟨initializedType⟩ ← observed (parts.initialized.type = .unit) "referenced initializedType"
  let ⟨storedType⟩ ← observed (parts.stored.type = .unit) "referenced storedType"
  let ⟨returnedType⟩ ← observed (parts.returned.type = .word) "referenced returnedType"
  return ⟨parts, parameters, inputTypes, returns, binderRequirements, targetScheme, targetRequirements, targetOwner,
    targetDistinct, initializedType, storedType, returnedType⟩

/-- The nodes of `bumped`'s body: its local `a` initialized by a literal of three reads of its parameter,
`a[value] = value`, `a[value] += value` and `a[value] ~=;`, each through the element of `a` at a read of the
parameter, the first two with a read of it on the right, and the return of `a[value]`, the element of a read of
`a` at one more read, found by following the statement graph. -/
structure BumpedParts (source : TypedSource) where
  binder : TypedBinder
  target : TypedBinder
  initialized : StatementNode
  assigned : StatementNode
  added : StatementNode
  flip : StatementNode
  returned : StatementNode
  assignedResolution : AssignmentResolution
  addedResolution : AssignmentResolution
  flipResolution : AssignmentResolution
  inputs : source.inputs = [binder]
  roots : source.roots = [.statement initialized.id, .statement assigned.id, .statement added.id,
    .statement flip.id, .statement returned.id]
  initializedFound : source.lookupStatement? initialized.id = some initialized
  assignedFound : source.lookupStatement? assigned.id = some assigned
  addedFound : source.lookupStatement? added.id = some added
  flipFound : source.lookupStatement? flip.id = some flip
  returnedFound : source.lookupStatement? returned.id = some returned
  first : Tests.SourceCoreNamedBranch.Read source binder .word
  second : Tests.SourceCoreNamedBranch.Read source binder .word
  third : Tests.SourceCoreNamedBranch.Read source binder .word
  literal : Tests.SourceCoreOperatorCalls.TypedNode source (TypeSystem.Ty.array .word)
  literalForm : literal.node.form = .arrayLiteral .word [first.node.id, second.node.id, third.node.id]
  initializedForm : initialized.form = .letDecl target (some literal.node.id)
  assignedKey : Tests.SourceCoreNamedBranch.Read source binder .word
  assignedValue : Tests.SourceCoreNamedBranch.Read source binder .word
  assignedForm : assigned.form = .assignValue assignedResolution .equal assignedValue.node.id
  assignedRoot : assignedResolution.target.root = target.id
  assignedProjections : assignedResolution.target.projections = [.element assignedKey.node.id]
  assignedTargetType : assignedResolution.target.type = .word
  addedKey : Tests.SourceCoreNamedBranch.Read source binder .word
  addedValue : Tests.SourceCoreNamedBranch.Read source binder .word
  addedForm : added.form = .assignValue addedResolution .add addedValue.node.id
  addedRoot : addedResolution.target.root = target.id
  addedProjections : addedResolution.target.projections = [.element addedKey.node.id]
  addedTargetType : addedResolution.target.type = .word
  flipKey : Tests.SourceCoreNamedBranch.Read source binder .word
  flipForm : flip.form = .assignBitNot flipResolution
  flipRoot : flipResolution.target.root = target.id
  flipProjections : flipResolution.target.projections = [.element flipKey.node.id]
  flipTargetType : flipResolution.target.type = .word
  readArray : Tests.SourceCoreNamedBranch.Read source target (TypeSystem.Ty.array .word)
  readIndex : Tests.SourceCoreNamedBranch.Read source binder .word
  read : Tests.SourceCoreOperatorCalls.TypedNode source .word
  readForm : read.node.form = .arrayIndex readArray.node.id readIndex.node.id
  returnedForm : returned.form = .returnStmt (some read.node.id)

def observeBumpedParts (source : TypedSource) : IO (BumpedParts source) := do
  let [binder] := source.inputs | throw (IO.userError "bumped input")
  let [.statement initializedId, .statement assignedId, .statement addedId, .statement flipId,
      .statement returnedId] := source.roots
    | throw (IO.userError "bumped roots")
  let some initialized := source.lookupStatement? initializedId | throw (IO.userError "bumped let")
  let some assigned := source.lookupStatement? assignedId | throw (IO.userError "bumped assignment")
  let some added := source.lookupStatement? addedId | throw (IO.userError "bumped compound assignment")
  let some flip := source.lookupStatement? flipId | throw (IO.userError "bumped flip")
  let some returned := source.lookupStatement? returnedId | throw (IO.userError "bumped return")
  let .letDecl target (some literalId) := initialized.form | throw (IO.userError "bumped let form")
  let .assignValue assignedResolution .equal assignedValueId := assigned.form
    | throw (IO.userError "bumped assignment form")
  let .assignValue addedResolution .add addedValueId := added.form
    | throw (IO.userError "bumped compound assignment form")
  let .assignBitNot flipResolution := flip.form | throw (IO.userError "bumped flip form")
  let .returnStmt (some readId) := returned.form | throw (IO.userError "bumped return form")
  let [.element assignedKeyId] := assignedResolution.target.projections
    | throw (IO.userError "bumped assignment projections")
  let [.element addedKeyId] := addedResolution.target.projections
    | throw (IO.userError "bumped compound assignment projections")
  let [.element flipKeyId] := flipResolution.target.projections | throw (IO.userError "bumped flip projections")
  let some literalNode := source.lookupExpression? literalId | throw (IO.userError "bumped literal")
  let .arrayLiteral _ [firstId, secondId, thirdId] := literalNode.form | throw (IO.userError "bumped literal form")
  let some firstNode := source.lookupExpression? firstId | throw (IO.userError "bumped first")
  let some secondNode := source.lookupExpression? secondId | throw (IO.userError "bumped second")
  let some thirdNode := source.lookupExpression? thirdId | throw (IO.userError "bumped third")
  let some assignedKeyNode := source.lookupExpression? assignedKeyId | throw (IO.userError "bumped assignment key")
  let some assignedValueNode := source.lookupExpression? assignedValueId
    | throw (IO.userError "bumped assignment value")
  let some addedKeyNode := source.lookupExpression? addedKeyId | throw (IO.userError "bumped compound key")
  let some addedValueNode := source.lookupExpression? addedValueId | throw (IO.userError "bumped compound value")
  let some flipKeyNode := source.lookupExpression? flipKeyId | throw (IO.userError "bumped flip key")
  let some readNode := source.lookupExpression? readId | throw (IO.userError "bumped read")
  let .arrayIndex readArrayId readIndexId := readNode.form | throw (IO.userError "bumped read form")
  let some readArrayNode := source.lookupExpression? readArrayId | throw (IO.userError "bumped read array")
  let some readIndexNode := source.lookupExpression? readIndexId | throw (IO.userError "bumped read index")
  let first ← Tests.SourceCoreNamedBranch.observeRead source binder firstNode .word
  let second ← Tests.SourceCoreNamedBranch.observeRead source binder secondNode .word
  let third ← Tests.SourceCoreNamedBranch.observeRead source binder thirdNode .word
  let literal ← Tests.SourceCoreOperatorCalls.observeNode source literalNode (TypeSystem.Ty.array .word)
  let ⟨literalForm⟩ ← observed (literal.node.form = .arrayLiteral .word [first.node.id, second.node.id, third.node.id])
    "bumped literalForm"
  let assignedKey ← Tests.SourceCoreNamedBranch.observeRead source binder assignedKeyNode .word
  let assignedValue ← Tests.SourceCoreNamedBranch.observeRead source binder assignedValueNode .word
  let addedKey ← Tests.SourceCoreNamedBranch.observeRead source binder addedKeyNode .word
  let addedValue ← Tests.SourceCoreNamedBranch.observeRead source binder addedValueNode .word
  let flipKey ← Tests.SourceCoreNamedBranch.observeRead source binder flipKeyNode .word
  let readArray ← Tests.SourceCoreNamedBranch.observeRead source target readArrayNode (TypeSystem.Ty.array .word)
  let readIndex ← Tests.SourceCoreNamedBranch.observeRead source binder readIndexNode .word
  let read ← Tests.SourceCoreOperatorCalls.observeNode source readNode .word
  let ⟨readForm⟩ ← observed (read.node.form = .arrayIndex readArray.node.id readIndex.node.id) "bumped readForm"
  let ⟨inputs⟩ ← observed (source.inputs = [binder]) "bumped inputs"
  let ⟨roots⟩ ← observed (source.roots = [.statement initialized.id, .statement assigned.id, .statement added.id,
    .statement flip.id, .statement returned.id]) "bumped roots shape"
  let ⟨initializedFound⟩ ← observed (source.lookupStatement? initialized.id = some initialized)
    "bumped initializedFound"
  let ⟨assignedFound⟩ ← observed (source.lookupStatement? assigned.id = some assigned) "bumped assignedFound"
  let ⟨addedFound⟩ ← observed (source.lookupStatement? added.id = some added) "bumped addedFound"
  let ⟨flipFound⟩ ← observed (source.lookupStatement? flip.id = some flip) "bumped flipFound"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "bumped returnedFound"
  let ⟨initializedForm⟩ ← observed (initialized.form = .letDecl target (some literal.node.id))
    "bumped initializedForm"
  let ⟨assignedForm⟩ ← observed (assigned.form = .assignValue assignedResolution .equal assignedValue.node.id)
    "bumped assignedForm"
  let ⟨assignedRoot⟩ ← observed (assignedResolution.target.root = target.id) "bumped assignedRoot"
  let ⟨assignedProjections⟩ ← observed (assignedResolution.target.projections = [.element assignedKey.node.id])
    "bumped assignedProjections"
  let ⟨assignedTargetType⟩ ← observed (assignedResolution.target.type = .word) "bumped assignedTargetType"
  let ⟨addedForm⟩ ← observed (added.form = .assignValue addedResolution .add addedValue.node.id) "bumped addedForm"
  let ⟨addedRoot⟩ ← observed (addedResolution.target.root = target.id) "bumped addedRoot"
  let ⟨addedProjections⟩ ← observed (addedResolution.target.projections = [.element addedKey.node.id])
    "bumped addedProjections"
  let ⟨addedTargetType⟩ ← observed (addedResolution.target.type = .word) "bumped addedTargetType"
  let ⟨flipForm⟩ ← observed (flip.form = .assignBitNot flipResolution) "bumped flipForm"
  let ⟨flipRoot⟩ ← observed (flipResolution.target.root = target.id) "bumped flipRoot"
  let ⟨flipProjections⟩ ← observed (flipResolution.target.projections = [.element flipKey.node.id])
    "bumped flipProjections"
  let ⟨flipTargetType⟩ ← observed (flipResolution.target.type = .word) "bumped flipTargetType"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some read.node.id)) "bumped returnedForm"
  return ⟨binder, target, initialized, assigned, added, flip, returned, assignedResolution, addedResolution,
    flipResolution, inputs, roots, initializedFound, assignedFound, addedFound, flipFound, returnedFound, first,
    second, third, literal, literalForm, initializedForm, assignedKey, assignedValue, assignedForm, assignedRoot,
    assignedProjections, assignedTargetType, addedKey, addedValue, addedForm, addedRoot, addedProjections,
    addedTargetType, flipKey, flipForm, flipRoot, flipProjections, flipTargetType, readArray, readIndex, read,
    readForm, returnedForm⟩

/-- `bumped`'s body: `let a: word[] = [value, value, value]`, `a[value] = value`, `a[value] += value` and
`a[value] ~=;` through the local's element, and the return of `a[value]`. -/
structure BumpedShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  parts : BumpedParts function.typedBody
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [.word]
  binderRequirements : parts.binder.schemeRequirements = []
  targetScheme : parts.target.scheme = .mono (TypeSystem.Ty.array .word)
  targetRequirements : parts.target.schemeRequirements = []
  targetOwner : parts.target.id.owner = function.typedBody.owner
  targetDistinct : parts.target.id ≠ parts.binder.id
  initializedType : parts.initialized.type = .unit
  assignedType : parts.assigned.type = .unit
  addedType : parts.added.type = .unit
  flipType : parts.flip.type = .unit
  returnedType : parts.returned.type = .word
  assignedRequirements : parts.assignedResolution.requirements = []
  addedRequirements : parts.addedResolution.requirements = []
  flipRequirements : parts.flipResolution.requirements = []

theorem BumpedShape.statementTyping {function : CheckedFunction} {signature : ProgramFunctionSignature}
    (shape : BumpedShape function signature) (signatures : ProgramSignatures) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.parts.initialized.id, shape.parts.assigned.id, shape.parts.added.id,
      shape.parts.flip.id, shape.parts.returned.id] :=
    statementRoots_injective (roots.symm.trans shape.parts.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type := .word, hasValue := true, sawReturn := true, control := .returned}
  let ordinary : StatementFacts := {type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit}
  refine ⟨BodyFacts.cons ordinary (BodyFacts.cons ordinary (BodyFacts.cons ordinary (BodyFacts.cons ordinary
    (BodyFacts.singleton facts)))), rfl, ?_⟩
  intro lexical extension
  rw [shape.parts.inputs, shape.inputTypes] at extension
  cases extension with
  | cons scheme head tail =>
    cases tail
    have binders : TypeParameterBindersWellFormed lexical := by
      rw [TypeParameterBindersWellFormed, head.context_fields.2.2.1]
      simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
        Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
    have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
    have array : TypeAdmissible lexical (TypeSystem.Ty.array .word) := ⟨binders, .array (.builtin .word)⟩
    have literalTyped := shape.parts.literal.ordinary array (by
      rw [shape.parts.literalForm]
      exact .arrayLiteral word
        (.cons (shape.parts.first.typed scheme shape.binderRequirements word head.local_self
            head.local_scheme_requirements_self)
          (.cons (shape.parts.second.typed scheme shape.binderRequirements word head.local_self
              head.local_scheme_requirements_self)
            (.cons (shape.parts.third.typed scheme shape.binderRequirements word head.local_self
                head.local_scheme_requirements_self) (.nil _)))))
    let locals := lexical.withLocal shape.parts.target.id shape.parts.target.scheme shape.parts.target.schemeRequirements
    have targetExtended : BinderExtends function.typedBody.owner lexical shape.parts.target locals := by
      apply BinderExtends.intro
      · exact {
          owned := shape.targetOwner
          scheme := shape.targetScheme.symm ▸ SchemeWellFormed.monoAdmissible array
          quantified_fresh := by rw [shape.targetScheme]; simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]
          monomorphic_requirements_empty := fun _ => shape.targetRequirements }
      · cases head
        simp [LocalFresh, Context.withLocal, checkedBodyContext, declarationContext,
          Context.ofSignatures, Context.forDeclaration, Context.withAssumptions,
          Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.targetDistinct]
    have initializedTyped : StatementHasType function.typedBody ⟨.word, 0⟩ lexical
        shape.parts.initialized.id locals ordinary := by
      apply StatementHasType.letInitialized (lookupStatement?_sound shape.parts.initializedFound)
        shape.parts.initializedForm
      · simpa only [shape.targetScheme, TypeSystem.Scheme.mono] using literalTyped
      · rw [shape.targetScheme]; rfl
      · rw [shape.targetScheme]; rfl
      · exact targetExtended
      · exact shape.initializedType
    have localWord : TypeAdmissible locals .word := ⟨binders, .builtin .word⟩
    have localArray : TypeAdmissible locals (TypeSystem.Ty.array .word) := ⟨binders, .array (.builtin .word)⟩
    have parameterLookup : locals.LocalLookup shape.parts.binder.id shape.parts.binder.scheme :=
      .tail shape.targetDistinct head.local_self
    have parameterRequirements :
        locals.LocalSchemeRequirementsLookup shape.parts.binder.id shape.parts.binder.schemeRequirements :=
      .tail shape.targetDistinct head.local_scheme_requirements_self
    have writable : WritableLocal locals shape.parts.target.id (TypeSystem.Ty.array .word) :=
      .intro targetExtended.local_self (shape.targetScheme.symm ▸ SchemeWellFormed.monoAdmissible localArray)
        (by rw [shape.targetScheme]; rfl) (by rw [shape.targetScheme]; rfl)
    -- The element of the local at a typed index is a `word` place.
    have place : ∀ {resolution : AssignmentResolution} {key : ExpressionId},
        resolution.target.root = shape.parts.target.id → resolution.target.projections = [.element key] →
        resolution.target.type = .word → ExpressionHasType function.typedBody locals key .word →
        SourcePlaceHasType function.typedBody locals resolution.target .word := by
      intro resolution key root projections type keyTyped
      refine .intro (rootType := TypeSystem.Ty.array .word) (by rw [root]; exact writable) ?_ type
      rw [projections]
      exact .element keyTyped (.nil _)
    have assignedKeyTyped := shape.parts.assignedKey.typed scheme shape.binderRequirements localWord parameterLookup
      parameterRequirements
    have assignedValueTyped := shape.parts.assignedValue.typed scheme shape.binderRequirements localWord
      parameterLookup parameterRequirements
    have assignedTyped : StatementHasType function.typedBody ⟨.word, 0⟩ locals shape.parts.assigned.id locals
        ordinary :=
      .assignValue (lookupStatement?_sound shape.parts.assignedFound) shape.parts.assignedForm
        (.equal (place shape.parts.assignedRoot shape.parts.assignedProjections shape.parts.assignedTargetType
          assignedKeyTyped) assignedValueTyped shape.assignedRequirements) shape.assignedType
    have addedKeyTyped := shape.parts.addedKey.typed scheme shape.binderRequirements localWord parameterLookup
      parameterRequirements
    have addedValueTyped := shape.parts.addedValue.typed scheme shape.binderRequirements localWord parameterLookup
      parameterRequirements
    have addedTyped : StatementHasType function.typedBody ⟨.word, 0⟩ locals shape.parts.added.id locals ordinary :=
      .assignValue (lookupStatement?_sound shape.parts.addedFound) shape.parts.addedForm
        (.wordCompound .add (place shape.parts.addedRoot shape.parts.addedProjections shape.parts.addedTargetType
          addedKeyTyped) addedValueTyped shape.addedRequirements) shape.addedType
    have flipKeyTyped := shape.parts.flipKey.typed scheme shape.binderRequirements localWord parameterLookup
      parameterRequirements
    have flipTyped : StatementHasType function.typedBody ⟨.word, 0⟩ locals shape.parts.flip.id locals ordinary :=
      .assignBitNot (lookupStatement?_sound shape.parts.flipFound) shape.parts.flipForm
        (.intro (place shape.parts.flipRoot shape.parts.flipProjections shape.parts.flipTargetType flipKeyTyped)
          .word shape.flipRequirements) shape.flipType
    have readArrayTyped := shape.parts.readArray.typed shape.targetScheme shape.targetRequirements localArray
      targetExtended.local_self targetExtended.local_scheme_requirements_self
    have readIndexTyped := shape.parts.readIndex.typed scheme shape.binderRequirements localWord parameterLookup
      parameterRequirements
    have readTyped := shape.parts.read.ordinary localWord (by
      rw [shape.parts.readForm]
      exact .arrayIndex readArrayTyped (.array .word) readIndexTyped .word)
    exact ⟨_, .cons initializedTyped (.cons assignedTyped (.cons addedTyped (.cons flipTyped (.singleton
      (.returnValue (lookupStatement?_sound shape.parts.returnedFound) shape.parts.returnedForm readTyped
        shape.returnedType)))))⟩

def observeBumped (function : CheckedFunction) (signature : ProgramFunctionSignature) :
    IO (BumpedShape function signature) := do
  let parts ← observeBumpedParts function.typedBody
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "bumped parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "bumped inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.word]) "bumped returns"
  let ⟨binderRequirements⟩ ← observed (parts.binder.schemeRequirements = []) "bumped binderRequirements"
  let ⟨targetScheme⟩ ← observed (parts.target.scheme = .mono (TypeSystem.Ty.array .word)) "bumped targetScheme"
  let ⟨targetRequirements⟩ ← observed (parts.target.schemeRequirements = []) "bumped targetRequirements"
  let ⟨targetOwner⟩ ← observed (parts.target.id.owner = function.typedBody.owner) "bumped targetOwner"
  let ⟨targetDistinct⟩ ← observed (parts.target.id ≠ parts.binder.id) "bumped targetDistinct"
  let ⟨initializedType⟩ ← observed (parts.initialized.type = .unit) "bumped initializedType"
  let ⟨assignedType⟩ ← observed (parts.assigned.type = .unit) "bumped assignedType"
  let ⟨addedType⟩ ← observed (parts.added.type = .unit) "bumped addedType"
  let ⟨flipType⟩ ← observed (parts.flip.type = .unit) "bumped flipType"
  let ⟨returnedType⟩ ← observed (parts.returned.type = .word) "bumped returnedType"
  let ⟨assignedRequirements⟩ ← observed (parts.assignedResolution.requirements = []) "bumped assignedRequirements"
  let ⟨addedRequirements⟩ ← observed (parts.addedResolution.requirements = []) "bumped addedRequirements"
  let ⟨flipRequirements⟩ ← observed (parts.flipResolution.requirements = []) "bumped flipRequirements"
  return ⟨parts, parameters, inputTypes, returns, binderRequirements, targetScheme, targetRequirements, targetOwner,
    targetDistinct, initializedType, assignedType, addedType, flipType, returnedType, assignedRequirements,
    addedRequirements, flipRequirements⟩

/-- Two members of a list of signatures whose ids are distinct are equal when
their ids are. -/
private theorem signature_of_id {signatures : List ProgramFunctionSignature}
    (distinct : (signatures.map (·.id)).Nodup) {first second : ProgramFunctionSignature}
    (firstMember : first ∈ signatures) (secondMember : second ∈ signatures) (same : first.id = second.id) :
    first = second := by
  induction signatures with
  | nil => cases firstMember
  | cons head rest ih =>
    obtain ⟨fresh, restDistinct⟩ := List.nodup_cons.mp distinct
    cases firstMember with
    | head =>
      cases secondMember with
      | head => rfl
      | tail _ secondRest => exact absurd (List.mem_map.mpr ⟨second, secondRest, same.symm⟩) fresh
    | tail _ firstRest =>
      cases secondMember with
      | head => exact absurd (List.mem_map.mpr ⟨first, firstRest, same⟩) fresh
      | tail _ secondRest => exact ih restDistinct firstRest secondRest

/-- The declarative typing of the complete checked program. -/
def observeWellFormed {program : CheckedProgram}
    (checked : checkProgram workspace options.checkingFuel = .ok program) :
    IO (PLift (ProgramWellFormed (Program.ofChecked program))) := do
  match functions : program.functions, signatures : program.signatures.functions with
  | [identityFunction, relayFunction, twiceFunction, narrowFunction, roundTripFunction, doubledFunction,
      shiftedFunction, flippedFunction, tailedFunction, storedFunction, summedFunction, zeroedFunction,
      invertedFunction, brokenFunction, countedFunction, tripledFunction, boxedFunction,
      filledFunction, listedFunction, slicedFunction, copiedFunction, referencedFunction, bumpedFunction],
    [identitySignature, relaySignature, twiceSignature, narrowSignature, roundTripSignature, doubledSignature,
      shiftedSignature, flippedSignature, tailedSignature, storedSignature, summedSignature, zeroedSignature,
      invertedSignature, brokenSignature, countedSignature, tripledSignature, boxedSignature,
      filledSignature, listedSignature, slicedSignature, copiedSignature, referencedSignature, bumpedSignature] =>
    let identityShape ← Tests.SourceCoreOperatorCalls.observeIdentity identityFunction identitySignature
    let relayShape ← observeRelay relayFunction relaySignature identitySignature
    let twiceShape ← observeTwice twiceFunction twiceSignature identitySignature
    let narrowShape ← observeNarrow narrowFunction narrowSignature
    let roundTripShape ← observeRoundTrip roundTripFunction roundTripSignature
    let doubledShape ← observeDoubled doubledFunction doubledSignature
    let shiftedShape ← observeShifted shiftedFunction shiftedSignature
    let flippedShape ← observeFlipped flippedFunction flippedSignature
    let tailedShape ← observeTailed tailedFunction tailedSignature identitySignature
    let storedShape ← observeStored storedFunction storedSignature
    let summedShape ← observeSummed summedFunction summedSignature
    let zeroedShape ← observeZeroed zeroedFunction zeroedSignature
    let invertedShape ← observeInverted invertedFunction invertedSignature
    let brokenShape ← observeBroken brokenFunction brokenSignature
    let countedShape ← observeCounted countedFunction countedSignature
    let tripledShape ← observeTripled tripledFunction tripledSignature
    let boxedShape ← observeBoxed boxedFunction boxedSignature program.signatures.dataTypes
    let filledShape ← observeFilled filledFunction filledSignature
    let listedShape ← observeListed listedFunction listedSignature
    let slicedShape ← observeSliced slicedFunction slicedSignature
    let copiedShape ← observeCopied copiedFunction copiedSignature
    let referencedShape ← observeReferenced referencedFunction referencedSignature
    let bumpedShape ← observeBumped bumpedFunction bumpedSignature
    let ⟨methods⟩ ← observed (program.methods = []) "calls methods"
    let ⟨identityDeclaration⟩ ← observed (identityFunction.declaration = identitySignature.id)
      "calls identityDeclaration"
    let ⟨relayDeclaration⟩ ← observed (relayFunction.declaration = relaySignature.id) "calls relayDeclaration"
    let ⟨twiceDeclaration⟩ ← observed (twiceFunction.declaration = twiceSignature.id) "calls twiceDeclaration"
    let ⟨narrowDeclaration⟩ ← observed (narrowFunction.declaration = narrowSignature.id) "calls narrowDeclaration"
    let ⟨roundTripDeclaration⟩ ← observed (roundTripFunction.declaration = roundTripSignature.id)
      "calls roundTripDeclaration"
    let ⟨doubledDeclaration⟩ ← observed (doubledFunction.declaration = doubledSignature.id) "calls doubledDeclaration"
    let ⟨shiftedDeclaration⟩ ← observed (shiftedFunction.declaration = shiftedSignature.id) "calls shiftedDeclaration"
    let ⟨flippedDeclaration⟩ ← observed (flippedFunction.declaration = flippedSignature.id) "calls flippedDeclaration"
    let ⟨tailedDeclaration⟩ ← observed (tailedFunction.declaration = tailedSignature.id) "calls tailedDeclaration"
    let ⟨storedDeclaration⟩ ← observed (storedFunction.declaration = storedSignature.id) "calls storedDeclaration"
    let ⟨summedDeclaration⟩ ← observed (summedFunction.declaration = summedSignature.id) "calls summedDeclaration"
    let ⟨zeroedDeclaration⟩ ← observed (zeroedFunction.declaration = zeroedSignature.id) "calls zeroedDeclaration"
    let ⟨invertedDeclaration⟩ ← observed (invertedFunction.declaration = invertedSignature.id)
      "calls invertedDeclaration"
    let ⟨brokenDeclaration⟩ ← observed (brokenFunction.declaration = brokenSignature.id) "calls brokenDeclaration"
    let ⟨countedDeclaration⟩ ← observed (countedFunction.declaration = countedSignature.id)
      "calls countedDeclaration"
    let ⟨tripledDeclaration⟩ ← observed (tripledFunction.declaration = tripledSignature.id)
      "calls tripledDeclaration"
    let ⟨boxedDeclaration⟩ ← observed (boxedFunction.declaration = boxedSignature.id)
      "calls boxedDeclaration"
    let ⟨filledDeclaration⟩ ← observed (filledFunction.declaration = filledSignature.id)
      "calls filledDeclaration"
    let ⟨listedDeclaration⟩ ← observed (listedFunction.declaration = listedSignature.id)
      "calls listedDeclaration"
    let ⟨slicedDeclaration⟩ ← observed (slicedFunction.declaration = slicedSignature.id)
      "calls slicedDeclaration"
    let ⟨copiedDeclaration⟩ ← observed (copiedFunction.declaration = copiedSignature.id)
      "calls copiedDeclaration"
    let ⟨referencedDeclaration⟩ ← observed (referencedFunction.declaration = referencedSignature.id)
      "calls referencedDeclaration"
    let ⟨bumpedDeclaration⟩ ← observed (bumpedFunction.declaration = bumpedSignature.id)
      "calls bumpedDeclaration"
    let ⟨distinct⟩ ← observed ((program.signatures.functions.map (·.id)).Nodup) "calls distinct signatures"
    let deep : CheckedProgramBodiesHaveStatementTyping program options.checkingFuel := {
      functions := by
        intro actual member candidate candidateMember accepted
        have declared := checkFunctionBody_success_declaration accepted
        have selects : ∀ {signature}, signature ∈ program.signatures.functions →
            actual.declaration = signature.id → candidate = signature := fun signatureMember same =>
          signature_of_id distinct candidateMember signatureMember (declared.symm.trans same)
        simp only [functions, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · obtain rfl := selects (by simp [signatures]) identityDeclaration
          exact identityShape.statementTyping program.signatures
        · obtain rfl := selects (by simp [signatures]) relayDeclaration
          exact relayShape.statementTyping program.signatures (by simp [signatures])
        · obtain rfl := selects (by simp [signatures]) twiceDeclaration
          exact twiceShape.statementTyping program.signatures (by simp [signatures])
        · obtain rfl := selects (by simp [signatures]) narrowDeclaration
          exact narrowShape.statementTyping program.signatures
        · obtain rfl := selects (by simp [signatures]) roundTripDeclaration
          exact roundTripShape.statementTyping program.signatures
        · obtain rfl := selects (by simp [signatures]) doubledDeclaration
          exact doubledShape.statementTyping program.signatures
        · obtain rfl := selects (by simp [signatures]) shiftedDeclaration
          exact shiftedShape.statementTyping program.signatures
        · obtain rfl := selects (by simp [signatures]) flippedDeclaration
          exact flippedShape.statementTyping program.signatures
        · obtain rfl := selects (by simp [signatures]) tailedDeclaration
          exact tailedShape.statementTyping program.signatures (by simp [signatures])
        · obtain rfl := selects (by simp [signatures]) storedDeclaration
          exact storedShape.statementTyping program.signatures
        · obtain rfl := selects (by simp [signatures]) summedDeclaration
          exact summedShape.statementTyping program.signatures
        · obtain rfl := selects (by simp [signatures]) zeroedDeclaration
          exact zeroedShape.statementTyping program.signatures
        · obtain rfl := selects (by simp [signatures]) invertedDeclaration
          exact invertedShape.statementTyping program.signatures
        · obtain rfl := selects (by simp [signatures]) brokenDeclaration
          exact brokenShape.statementTyping program.signatures
        · obtain rfl := selects (by simp [signatures]) countedDeclaration
          exact countedShape.statementTyping program.signatures
        · obtain rfl := selects (by simp [signatures]) tripledDeclaration
          exact tripledShape.statementTyping program.signatures
        · obtain rfl := selects (by simp [signatures]) boxedDeclaration
          exact boxedShape.statementTyping program.signatures rfl
        · obtain rfl := selects (by simp [signatures]) filledDeclaration
          exact filledShape.statementTyping program.signatures
        · obtain rfl := selects (by simp [signatures]) listedDeclaration
          exact listedShape.statementTyping program.signatures
        · obtain rfl := selects (by simp [signatures]) slicedDeclaration
          exact slicedShape.statementTyping program.signatures
        · obtain rfl := selects (by simp [signatures]) copiedDeclaration
          exact copiedShape.statementTyping program.signatures
        · obtain rfl := selects (by simp [signatures]) referencedDeclaration
          exact referencedShape.statementTyping program.signatures
        · obtain rfl := selects (by simp [signatures]) bumpedDeclaration
          exact bumpedShape.statementTyping program.signatures
      methods := by intro method member; simp only [methods, List.not_mem_nil] at member }
    return ⟨programWellFormed_ofCheckProgram_statements checked deep⟩
  | _, _ => throw (IO.userError "calls declaration count")

end Tests.SourceCoreAcceptedOneCall
end

section
/-! The cache rows of the twenty-three functions and their original Source
executions: `identity` returns its parameter, `relay` returns the direct call
of `identity` with its parameter, `twice` returns the direct call of
`identity` with that call, `tailed` ends in the direct call of `identity` with
its parameter as its final value, `stored` returns its parameter from the index of its local mapping
where its assignment put it, `summed` returns the integer sum of its parameter's word with itself,
`zeroed` returns the opcode `iszero` on its parameter, `inverted` returns the complement of the default
word from the index of its local mapping where its in-place `~` put it, `broken` and `counted` return
their parameter after their loops, `counted`'s after one iteration, `tripled` returns the triple of its
parameter, `boxed` returns `Item` applied to it, `filled` returns the length of a new array of its parameter's
length, `listed` its literal's element at its parameter, `sliced` its literal's slice's element there,
`copied` the element of its whole slice's copy there, `referenced` the element it stored through a memref into
its local literal, `bumped` the element its three writes left in its local literal there, the complement of twice
its parameter,
`narrow` returns the conversion of its parameter,
and `roundTrip` the word of that value, at a word canonical for `uint8`. Each call's global application is
a given body invocation. At a word not canonical for `uint8` the conversions of `narrow`, `doubled`,
`shifted` and `flipped` fault with the dirty-integer reason, and at a canonical word whose double is
outside `uint8`, `doubled`'s checked `x += x` panics with `0x11`. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreAcceptedOneCall
open Solcore Frontend SourceInference SourceSemantics
open Tests.SourceCoreAcceptedFixture (observed CompiledFixture)

/-- A heap with one more initialized `Word` cell. -/
def wordHeap (before : Dynamic.Heap) (word : Core.Word) : Dynamic.Heap :=
  ⟨before.cells ++ [{type := .word, value := some (.word word)}]⟩

/-- A binder at the next cell of a heap. -/
def wordEnvironment (binder : TypedBinder) (before : Dynamic.Heap) : Dynamic.Environment :=
  [(binder.id, ⟨before.cells.length⟩)]

/-- A heap with one more initialized `uint8` cell. -/
def byteHeap (before : Dynamic.Heap) (word : Core.Word) : Dynamic.Heap :=
  ⟨before.cells ++ [{type := .fixed ⟨false, .w8⟩, value := some (.word word)}]⟩

/-- A heap with one more `mapping(Word => Word)` cell. -/
def mappingHeap (before : Dynamic.Heap) (value : Option Dynamic.Value) : Dynamic.Heap :=
  ⟨before.cells ++ [{type := .mapping .word .word, value := value}]⟩

/-- A heap with one more initialized `bool` cell. -/
def boolHeap (before : Dynamic.Heap) (value : Bool) : Dynamic.Heap :=
  ⟨before.cells ++ [{type := .bool, value := some (.bool value)}]⟩

/-- `identity`'s cache row: its `Word` parameter, the read of it and the return
of the read. -/
structure IdentityBody (source : TypedSource) where
  binder : TypedBinder
  read : Tests.SourceCoreNamedBranch.Read source binder .word
  statement : StatementNode
  inputs : source.inputs = [binder]
  binderScheme : binder.scheme = .mono .word
  roots : source.roots = [.statement statement.id]
  statementFound : source.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some read.node.id)

def observeIdentityBody (source : TypedSource) : IO (IdentityBody source) := do
  let [binder] := source.inputs | throw (IO.userError "identity row input")
  let [.expression read, .statement statement] := source.nodes | throw (IO.userError "identity row nodes")
  let read ← Tests.SourceCoreNamedBranch.observeRead source binder read .word
  let ⟨inputs⟩ ← observed (source.inputs = [binder]) "identity row inputs"
  let ⟨binderScheme⟩ ← observed (binder.scheme = .mono .word) "identity row binderScheme"
  let ⟨roots⟩ ← observed (source.roots = [.statement statement.id]) "identity row roots"
  let ⟨statementFound⟩ ← observed (source.lookupStatement? statement.id = some statement)
    "identity row statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some read.node.id)) "identity row statementForm"
  return ⟨binder, read, statement, inputs, binderScheme, roots, statementFound, statementForm⟩

/-- `relay`'s cache row: its `Word` parameter, the read of it, the direct call
of `identity` with the read at the instantiation `target`, and the return of
the call. -/
structure RelayBody (fixture : CompiledFixture workspace options) (target : DeclarationInstantiation)
    (source : TypedSource) where
  identity : ProgramFunctionSignature
  member : identity ∈ fixture.recipe.compiled.sourceProgram.signatures.functions
  binder : TypedBinder
  read : Tests.SourceCoreNamedBranch.Read source binder .word
  call : Tests.SourceCoreDirectCalls.DirectCall source identity read.node.id .word
  selects : call.instantiation = target
  statement : StatementNode
  inputs : source.inputs = [binder]
  binderScheme : binder.scheme = .mono .word
  roots : source.roots = [.statement statement.id]
  statementFound : source.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some call.value.node.id)

/-- `twice`'s cache row: the nodes of `identity(identity(value))`, both calls
at the instantiation `target`. -/
structure TwiceBody (fixture : CompiledFixture workspace options) (target : DeclarationInstantiation)
    (source : TypedSource) where
  identity : ProgramFunctionSignature
  member : identity ∈ fixture.recipe.compiled.sourceProgram.signatures.functions
  parts : TwiceParts source identity
  binderScheme : parts.binder.scheme = .mono .word
  innerSelects : parts.inner.instantiation = target
  outerSelects : parts.outer.instantiation = target

/-- `tailed`'s cache row: its `Word` parameter, the read of it, the direct call
of `identity` with the read at the instantiation `target`, and the call as the
body's final value. -/
structure TailedBody (fixture : CompiledFixture workspace options) (target : DeclarationInstantiation)
    (source : TypedSource) where
  identity : ProgramFunctionSignature
  member : identity ∈ fixture.recipe.compiled.sourceProgram.signatures.functions
  binder : TypedBinder
  read : Tests.SourceCoreNamedBranch.Read source binder .word
  call : Tests.SourceCoreDirectCalls.DirectCall source identity read.node.id .word
  selects : call.instantiation = target
  statement : StatementNode
  inputs : source.inputs = [binder]
  binderScheme : binder.scheme = .mono .word
  roots : source.roots = [.statement statement.id]
  statementFound : source.lookupStatement? statement.id = some statement
  statementForm : statement.form = .expression call.value.node.id false

private def identitySignature (fixture : CompiledFixture workspace options) :
    IO {identity : ProgramFunctionSignature // identity ∈ fixture.recipe.compiled.sourceProgram.signatures.functions} := do
  match found : fixture.recipe.compiled.sourceProgram.signatures.functions.find?
      (fun signature => signature.name == "identity") with
  | none => throw (IO.userError "calls callee signature")
  | some identity => return ⟨identity, List.mem_of_find?_eq_some found⟩

def observeRelayBody (fixture : CompiledFixture workspace options) (target : DeclarationInstantiation)
    (source : TypedSource) : IO (RelayBody fixture target source) := do
  let ⟨identity, member⟩ ← identitySignature fixture
  let [binder] := source.inputs | throw (IO.userError "relay row input")
  let [.expression read, .expression callee, .expression value, .statement statement] := source.nodes
    | throw (IO.userError "relay row nodes")
  let read ← Tests.SourceCoreNamedBranch.observeRead source binder read .word
  let call ← Tests.SourceCoreDirectCalls.observeDirect source identity read.node.id callee value .word
  let ⟨selects⟩ ← observed (call.instantiation = target) "relay row call target"
  let ⟨inputs⟩ ← observed (source.inputs = [binder]) "relay row inputs"
  let ⟨binderScheme⟩ ← observed (binder.scheme = .mono .word) "relay row binderScheme"
  let ⟨roots⟩ ← observed (source.roots = [.statement statement.id]) "relay row roots"
  let ⟨statementFound⟩ ← observed (source.lookupStatement? statement.id = some statement)
    "relay row statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some call.value.node.id))
    "relay row statementForm"
  return ⟨identity, member, binder, read, call, selects, statement, inputs, binderScheme, roots, statementFound,
    statementForm⟩

def observeTailedBody (fixture : CompiledFixture workspace options) (target : DeclarationInstantiation)
    (source : TypedSource) : IO (TailedBody fixture target source) := do
  let ⟨identity, member⟩ ← identitySignature fixture
  let [binder] := source.inputs | throw (IO.userError "tailed row input")
  let [.statement statementId] := source.roots | throw (IO.userError "tailed row roots")
  let some statement := source.lookupStatement? statementId | throw (IO.userError "tailed row statement")
  let .expression valueId false := statement.form | throw (IO.userError "tailed row final value")
  let some valueNode := source.lookupExpression? valueId | throw (IO.userError "tailed row call node")
  let .call calleeId [readId] _ := valueNode.form | throw (IO.userError "tailed row call form")
  let some calleeNode := source.lookupExpression? calleeId | throw (IO.userError "tailed row callee")
  let some readNode := source.lookupExpression? readId | throw (IO.userError "tailed row read")
  let read ← Tests.SourceCoreNamedBranch.observeRead source binder readNode .word
  let call ← Tests.SourceCoreDirectCalls.observeDirect source identity read.node.id calleeNode valueNode .word
  let ⟨selects⟩ ← observed (call.instantiation = target) "tailed row call target"
  let ⟨inputs⟩ ← observed (source.inputs = [binder]) "tailed row inputs"
  let ⟨binderScheme⟩ ← observed (binder.scheme = .mono .word) "tailed row binderScheme"
  let ⟨roots⟩ ← observed (source.roots = [.statement statement.id]) "tailed row roots shape"
  let ⟨statementFound⟩ ← observed (source.lookupStatement? statement.id = some statement)
    "tailed row statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .expression call.value.node.id false)
    "tailed row statementForm"
  return ⟨identity, member, binder, read, call, selects, statement, inputs, binderScheme, roots, statementFound,
    statementForm⟩

def observeTwiceBody (fixture : CompiledFixture workspace options) (target : DeclarationInstantiation)
    (source : TypedSource) : IO (TwiceBody fixture target source) := do
  let ⟨identity, member⟩ ← identitySignature fixture
  let parts ← observeTwiceParts source identity
  let ⟨binderScheme⟩ ← observed (parts.binder.scheme = .mono .word) "twice row binderScheme"
  let ⟨innerSelects⟩ ← observed (parts.inner.instantiation = target) "twice row inner target"
  let ⟨outerSelects⟩ ← observed (parts.outer.instantiation = target) "twice row outer target"
  return ⟨identity, member, parts, binderScheme, innerSelects, outerSelects⟩

/-- `narrow`'s cache row: the nodes of `uint8(value)` at its `Word` parameter. -/
structure NarrowBody (source : TypedSource) where
  parts : NarrowParts source
  binderScheme : parts.binder.scheme = .mono .word

def observeNarrowBody (source : TypedSource) : IO (NarrowBody source) := do
  let parts ← observeNarrowParts source
  let ⟨binderScheme⟩ ← observed (parts.binder.scheme = .mono .word) "narrow row binderScheme"
  return ⟨parts, binderScheme⟩

/-- `roundTrip`'s cache row: the nodes of `Typedef.rep(uint8(value))` at its
`Word` parameter. -/
structure RoundTripBody (source : TypedSource) where
  parts : RoundTripParts source
  binderScheme : parts.binder.scheme = .mono .word

def observeRoundTripBody (source : TypedSource) : IO (RoundTripBody source) := do
  let parts ← observeRoundTripParts source
  let ⟨binderScheme⟩ ← observed (parts.binder.scheme = .mono .word) "roundTrip row binderScheme"
  return ⟨parts, binderScheme⟩

/-- `doubled`'s cache row: the nodes of its body, its `Word` parameter, and its `uint8` local, which
is the bare target of `x += x`. -/
structure DoubledBody (source : TypedSource) where
  parts : DoubledParts source
  binderScheme : parts.binder.scheme = .mono .word
  targetScheme : parts.target.scheme = .mono (.fixed ⟨false, .w8⟩)
  targetRoot : parts.resolution.target.root = parts.target.id
  targetType : parts.resolution.target.type = .fixed ⟨false, .w8⟩
  targetBare : parts.resolution.target.projections = []

def observeDoubledBody (source : TypedSource) : IO (DoubledBody source) := do
  let parts ← observeDoubledParts source
  let ⟨binderScheme⟩ ← observed (parts.binder.scheme = .mono .word) "doubled row binderScheme"
  let ⟨targetScheme⟩ ← observed (parts.target.scheme = .mono (.fixed ⟨false, .w8⟩)) "doubled row targetScheme"
  let ⟨targetRoot⟩ ← observed (parts.resolution.target.root = parts.target.id) "doubled row targetRoot"
  let ⟨targetType⟩ ← observed (parts.resolution.target.type = .fixed ⟨false, .w8⟩) "doubled row targetType"
  let ⟨targetBare⟩ ← observed (parts.resolution.target.projections = []) "doubled row targetBare"
  return ⟨parts, binderScheme, targetScheme, targetRoot, targetType, targetBare⟩

/-- `shifted`'s cache row: the nodes of its body, its `Word` parameter and its `uint8` local. -/
structure ShiftedBody (source : TypedSource) where
  parts : ShiftedParts source
  binderScheme : parts.binder.scheme = .mono .word
  targetScheme : parts.target.scheme = .mono (.fixed ⟨false, .w8⟩)

def observeShiftedBody (source : TypedSource) : IO (ShiftedBody source) := do
  let parts ← observeShiftedParts source
  let ⟨binderScheme⟩ ← observed (parts.binder.scheme = .mono .word) "shifted row binderScheme"
  let ⟨targetScheme⟩ ← observed (parts.target.scheme = .mono (.fixed ⟨false, .w8⟩)) "shifted row targetScheme"
  return ⟨parts, binderScheme, targetScheme⟩

/-- `flipped`'s cache row: the nodes of its body, its `Word` parameter and its `uint8` local. -/
structure FlippedBody (source : TypedSource) where
  parts : FlippedParts source
  binderScheme : parts.binder.scheme = .mono .word
  targetScheme : parts.target.scheme = .mono (.fixed ⟨false, .w8⟩)

def observeFlippedBody (source : TypedSource) : IO (FlippedBody source) := do
  let parts ← observeFlippedParts source
  let ⟨binderScheme⟩ ← observed (parts.binder.scheme = .mono .word) "flipped row binderScheme"
  let ⟨targetScheme⟩ ← observed (parts.target.scheme = .mono (.fixed ⟨false, .w8⟩)) "flipped row targetScheme"
  return ⟨parts, binderScheme, targetScheme⟩

/-- `stored`'s cache row: the nodes of its body, its `Word` parameter and its local mapping. -/
structure StoredBody (source : TypedSource) where
  parts : StoredParts source
  binderScheme : parts.binder.scheme = .mono .word
  tableScheme : parts.table.scheme = .mono (.mapping .word .word)
  tableDistinct : parts.table.id ≠ parts.binder.id

def observeStoredBody (source : TypedSource) : IO (StoredBody source) := do
  let parts ← observeStoredParts source
  let ⟨binderScheme⟩ ← observed (parts.binder.scheme = .mono .word) "stored row binderScheme"
  let ⟨tableScheme⟩ ← observed (parts.table.scheme = .mono (.mapping .word .word)) "stored row tableScheme"
  let ⟨tableDistinct⟩ ← observed (parts.table.id ≠ parts.binder.id) "stored row tableDistinct"
  return ⟨parts, binderScheme, tableScheme, tableDistinct⟩

/-- `summed`'s cache row: the nodes of its body and its `Word` parameter. -/
structure SummedBody (source : TypedSource) where
  parts : SummedParts source
  binderScheme : parts.binder.scheme = .mono .word

def observeSummedBody (source : TypedSource) : IO (SummedBody source) := do
  let parts ← observeSummedParts source
  let ⟨binderScheme⟩ ← observed (parts.binder.scheme = .mono .word) "summed row binderScheme"
  return ⟨parts, binderScheme⟩

/-- `zeroed`'s cache row: the nodes of `iszero(value)` at its `Word` parameter. -/
structure ZeroedBody (source : TypedSource) where
  parts : ZeroedParts source
  binderScheme : parts.binder.scheme = .mono .word

def observeZeroedBody (source : TypedSource) : IO (ZeroedBody source) := do
  let parts ← observeZeroedParts source
  let ⟨binderScheme⟩ ← observed (parts.binder.scheme = .mono .word) "zeroed row binderScheme"
  return ⟨parts, binderScheme⟩

/-- `inverted`'s cache row: the nodes of its body, its `Word` parameter and its local mapping. -/
structure InvertedBody (source : TypedSource) where
  parts : InvertedParts source
  binderScheme : parts.binder.scheme = .mono .word
  tableScheme : parts.table.scheme = .mono (.mapping .word .word)
  tableDistinct : parts.table.id ≠ parts.binder.id

def observeInvertedBody (source : TypedSource) : IO (InvertedBody source) := do
  let parts ← observeInvertedParts source
  let ⟨binderScheme⟩ ← observed (parts.binder.scheme = .mono .word) "inverted row binderScheme"
  let ⟨tableScheme⟩ ← observed (parts.table.scheme = .mono (.mapping .word .word)) "inverted row tableScheme"
  let ⟨tableDistinct⟩ ← observed (parts.table.id ≠ parts.binder.id) "inverted row tableDistinct"
  return ⟨parts, binderScheme, tableScheme, tableDistinct⟩

/-- `broken`'s cache row: the nodes of its body and its `Word` parameter. -/
structure BrokenBody (source : TypedSource) where
  parts : BrokenParts source
  binderScheme : parts.binder.scheme = .mono .word

def observeBrokenBody (source : TypedSource) : IO (BrokenBody source) := do
  let parts ← observeBrokenParts source
  let ⟨binderScheme⟩ ← observed (parts.binder.scheme = .mono .word) "broken row binderScheme"
  return ⟨parts, binderScheme⟩

/-- `counted`'s cache row: the nodes of its body, its `Word` parameter and the
header's `bool` local. -/
structure CountedBody (source : TypedSource) where
  parts : CountedParts source
  binderScheme : parts.binder.scheme = .mono .word
  goScheme : parts.go.scheme = .mono .bool
  goDistinct : parts.go.id ≠ parts.binder.id

def observeCountedBody (source : TypedSource) : IO (CountedBody source) := do
  let parts ← observeCountedParts source
  let ⟨binderScheme⟩ ← observed (parts.binder.scheme = .mono .word) "counted row binderScheme"
  let ⟨goScheme⟩ ← observed (parts.go.scheme = .mono .bool) "counted row goScheme"
  let ⟨goDistinct⟩ ← observed (parts.go.id ≠ parts.binder.id) "counted row goDistinct"
  return ⟨parts, binderScheme, goScheme, goDistinct⟩

/-- `tripled`'s cache row: the nodes of its body and its `Word` parameter. -/
structure TripledBody (source : TypedSource) where
  parts : TripledParts source
  binderScheme : parts.binder.scheme = .mono .word

def observeTripledBody (source : TypedSource) : IO (TripledBody source) := do
  let parts ← observeTripledParts source
  let ⟨binderScheme⟩ ← observed (parts.binder.scheme = .mono .word) "tripled row binderScheme"
  return ⟨parts, binderScheme⟩

/-- `boxed`'s cache row: the nodes of its body and its `Word` parameter. -/
structure BoxedBody (source : TypedSource) where
  parts : BoxedParts source
  binderScheme : parts.binder.scheme = .mono .word

def observeBoxedBody (source : TypedSource) : IO (BoxedBody source) := do
  let parts ← observeBoxedParts source
  let ⟨binderScheme⟩ ← observed (parts.binder.scheme = .mono .word) "boxed row binderScheme"
  return ⟨parts, binderScheme⟩

/-- `filled`'s cache row: the nodes of its body and its `Word` parameter. -/
structure FilledBody (source : TypedSource) where
  parts : FilledParts source
  binderScheme : parts.binder.scheme = .mono .word

def observeFilledBody (source : TypedSource) : IO (FilledBody source) := do
  let parts ← observeFilledParts source
  let ⟨binderScheme⟩ ← observed (parts.binder.scheme = .mono .word) "filled row binderScheme"
  return ⟨parts, binderScheme⟩

/-- `listed`'s cache row: the nodes of its body and its `Word` parameter. -/
structure ListedBody (source : TypedSource) where
  parts : ListedParts source
  binderScheme : parts.binder.scheme = .mono .word

def observeListedBody (source : TypedSource) : IO (ListedBody source) := do
  let parts ← observeListedParts source
  let ⟨binderScheme⟩ ← observed (parts.binder.scheme = .mono .word) "listed row binderScheme"
  return ⟨parts, binderScheme⟩

/-- `sliced`'s cache row: the nodes of its body and its `Word` parameter. -/
structure SlicedBody (source : TypedSource) where
  parts : SlicedParts source
  binderScheme : parts.binder.scheme = .mono .word

def observeSlicedBody (source : TypedSource) : IO (SlicedBody source) := do
  let parts ← observeSlicedParts source
  let ⟨binderScheme⟩ ← observed (parts.binder.scheme = .mono .word) "sliced row binderScheme"
  return ⟨parts, binderScheme⟩

/-- `copied`'s cache row: the nodes of its body and its `Word` parameter. -/
structure CopiedBody (source : TypedSource) where
  parts : CopiedParts source
  binderScheme : parts.binder.scheme = .mono .word

def observeCopiedBody (source : TypedSource) : IO (CopiedBody source) := do
  let parts ← observeCopiedParts source
  let ⟨binderScheme⟩ ← observed (parts.binder.scheme = .mono .word) "copied row binderScheme"
  return ⟨parts, binderScheme⟩

/-- `referenced`'s cache row: the nodes of its body and its `Word` parameter. -/
structure ReferencedBody (source : TypedSource) where
  parts : ReferencedParts source
  binderScheme : parts.binder.scheme = .mono .word

def observeReferencedBody (source : TypedSource) : IO (ReferencedBody source) := do
  let parts ← observeReferencedParts source
  let ⟨binderScheme⟩ ← observed (parts.binder.scheme = .mono .word) "referenced row binderScheme"
  return ⟨parts, binderScheme⟩

/-- `bumped`'s cache row: the nodes of its body and its `word` parameter. -/
structure BumpedBody (source : TypedSource) where
  parts : BumpedParts source
  binderScheme : parts.binder.scheme = .mono .word

def observeBumpedBody (source : TypedSource) : IO (BumpedBody source) := do
  let parts ← observeBumpedParts source
  let ⟨binderScheme⟩ ← observed (parts.binder.scheme = .mono .word) "bumped row binderScheme"
  return ⟨parts, binderScheme⟩

/-- The read of a parameter at the next cell of a heap. -/
theorem read_value {source : TypedSource} {binder : TypedBinder}
    (read : Tests.SourceCoreNamedBranch.Read source binder .word) {program : SourceSemantics.Program}
    {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment) (before : Dynamic.Heap)
    (word : Core.Word) :
    Dynamic.ExpressionEvaluates program context evidence source (wordEnvironment binder before)
      (wordHeap before word) read.node.id (.word word) (wordHeap before word) := by
  have allocation : Dynamic.Heap.Allocates before .word (some (.word word)) ⟨before.cells.length⟩
      (wordHeap before word) := .append
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound read.found)
  · rw [read.form]
    exact .local (by rw [read.requirements, read.coercions]; rfl) Dynamic.Environment.LooksUp.head
      allocation.reads_new rfl rfl
  · rw [read.coercions]
    exact .nil

/-- A direct call of a monomorphic declaration with one argument evaluates to
its global application's result, given the argument's execution and the
call's validity. -/
theorem call_value {source : TypedSource} {identity : ProgramFunctionSignature} {argument : ExpressionId}
    (call : Tests.SourceCoreDirectCalls.DirectCall source identity argument .word)
    {program : SourceSemantics.Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before middle after : Dynamic.Heap} {input output : Dynamic.Value}
    (argumentTrace : Dynamic.ExpressionEvaluates program context evidence source environment before argument input
      middle)
    (valid : SourceSemantics.DeclarationInstantiation.Valid context call.instantiation)
    (applies : Dynamic.CallableApplies program context evidence [] middle (.global ⟨call.instantiation, []⟩)
      [input] output after) :
    Dynamic.ExpressionEvaluates program context evidence source environment before call.value.node.id output after := by
  have predicates : call.instantiation.predicates = [] := by
    simp [call.exact]
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound call.value.found)
  · rw [call.form, call.value.requirements, call.value.coercions]
    exact .directCall (lookupExpression?_sound call.callee.found) call.calleeForm call.callee.requirements
      call.callee.coercions valid (.cons argumentTrace .nil)
      (by
        rw [predicates]
        exact .intro (selected := []) (contextual := []) (signatureRequirements := []) rfl rfl .nil)
      applies
  · rw [call.value.coercions]
    exact .nil

/-- A direct call's validity at any context whose signatures have the callee. -/
theorem call_valid {source : TypedSource} {identity : ProgramFunctionSignature} {argument : ExpressionId}
    (call : Tests.SourceCoreDirectCalls.DirectCall source identity argument .word)
    {context : SourceSemantics.Context} (member : identity ∈ context.signatures.functions) :
    SourceSemantics.DeclarationInstantiation.Valid context call.instantiation := by
  rw [call.exact]
  refine .intro identity member rfl ?_ ?_ ?_ ?_ rfl rfl
  · simpa only [call.scheme] using SourceSemantics.ParameterSubstitution.exact_empty
  · intro name value found
    cases found
  · simp [call.scheme]
  · simp [call.scheme]

/-- `identity`'s body returns its parameter's value. -/
theorem IdentityBody.trace {source : TypedSource} (body : IdentityBody source) {program : SourceSemantics.Program}
    {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment) (before : Dynamic.Heap)
    (word : Core.Word) :
    Dynamic.FunctionStatementsExecute program context evidence source (wordEnvironment body.binder before)
      (wordHeap before word) [body.statement.id] context (.returned (.word word)) (wordHeap before word) := by
  apply Dynamic.FunctionStatementsExecute.singleton (lookupStatement?_sound body.statementFound)
  · intro expression impossible
    rw [body.statementForm] at impossible
    cases impossible
  · exact .returnValue (lookupStatement?_sound body.statementFound) body.statementForm
      (read_value body.read evidence before word)

/-- `relay`'s body returns the value of its direct call, given the call's
validity and its global application. -/
theorem RelayBody.trace {fixture : CompiledFixture workspace options} {target : DeclarationInstantiation}
    {source : TypedSource} (body : RelayBody fixture target source) {program : SourceSemantics.Program}
    {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment) (before : Dynamic.Heap)
    (word : Core.Word) (valid : SourceSemantics.DeclarationInstantiation.Valid context body.call.instantiation)
    {after : Dynamic.Heap}
    (applies : Dynamic.CallableApplies program context evidence [] (wordHeap before word)
      (.global ⟨body.call.instantiation, []⟩) [.word word] (.word word) after) :
    Dynamic.FunctionStatementsExecute program context evidence source (wordEnvironment body.binder before)
      (wordHeap before word) [body.statement.id] context (.returned (.word word)) after := by
  apply Dynamic.FunctionStatementsExecute.singleton (lookupStatement?_sound body.statementFound)
  · intro expression impossible
    rw [body.statementForm] at impossible
    cases impossible
  · exact .returnValue (lookupStatement?_sound body.statementFound) body.statementForm
      (call_value body.call (read_value body.read evidence before word) valid applies)

/-- `tailed`'s body ends in the value of its direct call, given the call's
validity and its global application. -/
theorem TailedBody.trace {fixture : CompiledFixture workspace options} {target : DeclarationInstantiation}
    {source : TypedSource} (body : TailedBody fixture target source) {program : SourceSemantics.Program}
    {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment) (before : Dynamic.Heap)
    (word : Core.Word) (valid : SourceSemantics.DeclarationInstantiation.Valid context body.call.instantiation)
    {after : Dynamic.Heap}
    (applies : Dynamic.CallableApplies program context evidence [] (wordHeap before word)
      (.global ⟨body.call.instantiation, []⟩) [.word word] (.word word) after) :
    Dynamic.FunctionStatementsExecute program context evidence source (wordEnvironment body.binder before)
      (wordHeap before word) [body.statement.id] context (.returned (.word word)) after :=
  .tailExpression (lookupStatement?_sound body.statementFound) body.statementForm
    (call_value body.call (read_value body.read evidence before word) valid applies)

/-- `twice`'s body returns the value of its outer call, given both calls'
validity and global applications. -/
theorem TwiceBody.trace {fixture : CompiledFixture workspace options} {target : DeclarationInstantiation}
    {source : TypedSource} (body : TwiceBody fixture target source) {program : SourceSemantics.Program}
    {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment) (before : Dynamic.Heap)
    (word : Core.Word)
    (innerValid : SourceSemantics.DeclarationInstantiation.Valid context body.parts.inner.instantiation)
    (outerValid : SourceSemantics.DeclarationInstantiation.Valid context body.parts.outer.instantiation)
    {middle after : Dynamic.Heap}
    (innerApplies : Dynamic.CallableApplies program context evidence [] (wordHeap before word)
      (.global ⟨body.parts.inner.instantiation, []⟩) [.word word] (.word word) middle)
    (outerApplies : Dynamic.CallableApplies program context evidence [] middle
      (.global ⟨body.parts.outer.instantiation, []⟩) [.word word] (.word word) after) :
    Dynamic.FunctionStatementsExecute program context evidence source (wordEnvironment body.parts.binder before)
      (wordHeap before word) [body.parts.statement.id] context (.returned (.word word)) after := by
  apply Dynamic.FunctionStatementsExecute.singleton (lookupStatement?_sound body.parts.statementFound)
  · intro expression impossible
    rw [body.parts.statementForm] at impossible
    cases impossible
  · exact .returnValue (lookupStatement?_sound body.parts.statementFound) body.parts.statementForm
      (call_value body.parts.outer
        (call_value body.parts.inner (read_value body.parts.read evidence before word) innerValid innerApplies)
        outerValid outerApplies)

/-- A conversion of an argument evaluates to the word that its Source
application gives the argument's word. -/
theorem conversion_value {source : TypedSource} {function : BuiltinFunctionId} {argument : ExpressionId}
    (converted : Tests.SourceCoreBuiltinCalls.BuiltinCall source function argument)
    {program : SourceSemantics.Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {word : Core.Word}
    (argumentTrace : Dynamic.ExpressionEvaluates program context evidence source environment before argument
      (.word word) after)
    (applied : Dynamic.BuiltinApplies function [.word word] (.word word)) :
    Dynamic.ExpressionEvaluates program context evidence source environment before converted.value.node.id
      (.word word) after := by
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound converted.value.found)
  · rw [converted.form, converted.value.requirements, converted.value.coercions]
    exact .builtinCall rfl (.cons argumentTrace .nil) (.builtin applied)
  · rw [converted.value.coercions]
    exact .nil

/-- `narrow`'s body returns a canonical parameter word. -/
theorem NarrowBody.trace {source : TypedSource} (body : NarrowBody source) {program : SourceSemantics.Program}
    {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment) (before : Dynamic.Heap)
    (word : Core.Word) (canonical : TypeSystem.FixedInteger.canonical ⟨false, .w8⟩ word.val = true) :
    Dynamic.FunctionStatementsExecute program context evidence source (wordEnvironment body.parts.binder before)
      (wordHeap before word) [body.parts.statement.id] context (.returned (.word word)) (wordHeap before word) := by
  apply Dynamic.FunctionStatementsExecute.singleton (lookupStatement?_sound body.parts.statementFound)
  · intro expression impossible
    rw [body.parts.statementForm] at impossible
    cases impossible
  · exact .returnValue (lookupStatement?_sound body.parts.statementFound) body.parts.statementForm
      (conversion_value body.parts.converted (read_value body.parts.read evidence before word)
        (.fixedFromWord canonical))

/-- `roundTrip`'s body returns a parameter word canonical for `uint8`: the
conversion gives the value, and `Typedef.rep` its word. -/
theorem RoundTripBody.trace {source : TypedSource} (body : RoundTripBody source) {program : SourceSemantics.Program}
    {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment) (before : Dynamic.Heap)
    (word : Core.Word) (canonical : TypeSystem.FixedInteger.canonical ⟨false, .w8⟩ word.val = true) :
    Dynamic.FunctionStatementsExecute program context evidence source (wordEnvironment body.parts.binder before)
      (wordHeap before word) [body.parts.statement.id] context (.returned (.word word)) (wordHeap before word) := by
  apply Dynamic.FunctionStatementsExecute.singleton (lookupStatement?_sound body.parts.statementFound)
  · intro expression impossible
    rw [body.parts.statementForm] at impossible
    cases impossible
  · exact .returnValue (lookupStatement?_sound body.parts.statementFound) body.parts.statementForm
      (conversion_value body.parts.represented
        (conversion_value body.parts.narrowed (read_value body.parts.read evidence before word)
          (.fixedFromWord canonical))
        (.fixedToWord canonical))

/-- A conversion of an argument faults with the reason that its Source
application gives the argument's word. -/
theorem conversion_fault {source : TypedSource} {function : BuiltinFunctionId} {argument : ExpressionId}
    (converted : Tests.SourceCoreBuiltinCalls.BuiltinCall source function argument)
    {program : SourceSemantics.Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {word : Core.Word}
    (argumentTrace : Dynamic.ExpressionEvaluates program context evidence source environment before argument
      (.word word) after)
    {reason : Dynamic.SemanticFault} (failed : Dynamic.BuiltinFaults function [.word word] reason) :
    Dynamic.ExpressionFaults program context evidence source environment before converted.value.node.id reason
      after := by
  apply Dynamic.ExpressionFaults.form (lookupExpression?_sound converted.value.found)
  rw [converted.form, converted.value.requirements, converted.value.coercions]
  exact .builtinApply rfl (.cons argumentTrace .nil) (.builtinFaults failed)

/-- `narrow`'s body faults at a parameter word not canonical for `uint8`: its
conversion gives the dirty-integer reason. -/
theorem NarrowBody.fault {source : TypedSource} (body : NarrowBody source) {program : SourceSemantics.Program}
    {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment) (before : Dynamic.Heap)
    (word : Core.Word) (dirty : TypeSystem.FixedInteger.canonical ⟨false, .w8⟩ word.val = false) :
    Dynamic.FunctionStatementsFault program context evidence source (wordEnvironment body.parts.binder before)
      (wordHeap before word) [body.parts.statement.id] context .dirtyHigherBitsForInteger (wordHeap before word) :=
  .singleton (.returnValue (lookupStatement?_sound body.parts.statementFound) body.parts.statementForm
    (conversion_fault body.parts.converted (read_value body.parts.read evidence before word) (.fixedFromWord dirty)))

/-- A body whose first statement initializes a `uint8` local with the
conversion of its `Word` parameter, before at least one more statement, faults
there at a parameter word not canonical for `uint8`. -/
theorem dirty_initializer {source : TypedSource} {binder target : TypedBinder}
    (read : Tests.SourceCoreNamedBranch.Read source binder .word)
    (converted : Tests.SourceCoreBuiltinCalls.BuiltinCall source (.fixedFromWord ⟨false, .w8⟩) read.node.id)
    {initialized : StatementNode} (found : source.lookupStatement? initialized.id = some initialized)
    (form : initialized.form = .letDecl target (some converted.value.node.id))
    (scheme : target.scheme = .mono (.fixed ⟨false, .w8⟩)) {program : SourceSemantics.Program}
    {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment) (before : Dynamic.Heap)
    (word : Core.Word) (dirty : TypeSystem.FixedInteger.canonical ⟨false, .w8⟩ word.val = false)
    (next : StatementId) (rest : List StatementId) :
    Dynamic.FunctionStatementsFault program context evidence source (wordEnvironment binder before)
      (wordHeap before word) (initialized.id :: next :: rest) context .dirtyHigherBitsForInteger
      (wordHeap before word) :=
  .head (.letInitializer (lookupStatement?_sound found) form (by rw [scheme]; rfl)
    (conversion_fault converted (read_value read evidence before word) (.fixedFromWord dirty)))

/-- `doubled`'s body panics with `0x11` at a parameter word canonical for
`uint8` whose double is outside `uint8`: its local holds the word, and the
checked `x += x` overflows. The local's context is a binder extension of the
body's. -/
theorem DoubledBody.panic {source : TypedSource} (body : DoubledBody source) {program : SourceSemantics.Program}
    {context localContext : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
    (before : Dynamic.Heap) (extension : BinderExtends source.owner context body.parts.target localContext)
    (word : Core.Word) (canonical : TypeSystem.FixedInteger.canonical ⟨false, .w8⟩ word.val = true)
    (outside : ¬ Dynamic.FixedInRange ⟨false, .w8⟩
      (Dynamic.checkedResult .add (Dynamic.fixedValue ⟨false, .w8⟩ word) (Dynamic.fixedValue ⟨false, .w8⟩ word))) :
    Dynamic.FunctionStatementsFault program context evidence source (wordEnvironment body.parts.binder before)
      (wordHeap before word) [body.parts.initialized.id, body.parts.assignment.id, body.parts.returned.id]
      localContext (.panic 0x11) (byteHeap (wordHeap before word) word) := by
  have allocation : Dynamic.Heap.Allocates (wordHeap before word) (.fixed ⟨false, .w8⟩) (some (.word word))
      ⟨(wordHeap before word).cells.length⟩ (byteHeap (wordHeap before word) word) := .append
  have declared : Dynamic.StatementExecutes program context evidence source
      (wordEnvironment body.parts.binder before) (wordHeap before word) body.parts.initialized.id localContext
      (.fallthrough ((body.parts.target.id, ⟨(wordHeap before word).cells.length⟩) ::
        wordEnvironment body.parts.binder before)) (byteHeap (wordHeap before word) word) :=
    .letInitialized (lookupStatement?_sound body.parts.initializedFound) body.parts.initializedForm
      (conversion_value body.parts.converted (read_value body.parts.read evidence before word)
        (.fixedFromWord canonical))
      (by rw [body.targetScheme]; rfl) extension (by rw [body.targetScheme]; exact allocation)
  have resolve : Dynamic.SourcePlaceResolves program localContext evidence source
      ((body.parts.target.id, ⟨(wordHeap before word).cells.length⟩) :: wordEnvironment body.parts.binder before)
      (byteHeap (wordHeap before word) word) body.parts.resolution.target
      {location := ⟨(wordHeap before word).cells.length⟩, rootType := .fixed ⟨false, .w8⟩,
        valueType := body.parts.resolution.target.type, projections := [], selected := some (.word word)}
      (byteHeap (wordHeap before word) word) := by
    apply Dynamic.SourcePlaceResolves.intro (initialCell := {type := .fixed ⟨false, .w8⟩, value := some (.word word)})
      (currentCell := {type := .fixed ⟨false, .w8⟩, value := some (.word word)})
    · rw [body.targetRoot]
      exact .head
    · exact allocation.reads_new
    · rw [body.targetBare]
      exact .nil
    · exact allocation.reads_new
    · exact .initialized
    · exact .nil
  have right : Dynamic.ExpressionEvaluates program localContext evidence source
      ((body.parts.target.id, ⟨(wordHeap before word).cells.length⟩) :: wordEnvironment body.parts.binder before)
      (byteHeap (wordHeap before word) word) body.parts.rightRead.node.id (.word word)
      (byteHeap (wordHeap before word) word) := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound body.parts.rightRead.found)
    · rw [body.parts.rightRead.form]
      exact .local (by rw [body.parts.rightRead.requirements, body.parts.rightRead.coercions]; rfl)
        Dynamic.Environment.LooksUp.head allocation.reads_new rfl rfl
    · rw [body.parts.rightRead.coercions]
      exact .nil
  have panics : Dynamic.AssignmentOperandsPanic body.parts.resolution.target.type .add (some (.word word))
      (.word word) 0x11 :=
    .compound .add (.fixed (by rw [body.targetType]) (.overflow .add word word outside))
  exact .tail declared (.head (.assignValue (lookupStatement?_sound body.parts.assignmentFound)
    body.parts.assignmentForm (.panic resolve right allocation.reads_new rfl .initialized .nil panics)))

private theorem write_last (cells : List Dynamic.Cell) (old next : Dynamic.Cell) :
    Dynamic.Heap.CellsWrite (cells ++ [old]) cells.length next (cells ++ [next]) := by
  induction cells with
  | nil => exact .head
  | cons head rest ih => exact .tail ih

/-- The read of a local evaluates to its cell's value. -/
theorem local_value {source : TypedSource} {binder : TypedBinder} {type : TypeSystem.Ty}
    (read : Tests.SourceCoreNamedBranch.Read source binder type) {program : SourceSemantics.Program}
    {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment) {environment : Dynamic.Environment}
    {heap : Dynamic.Heap} {location : Dynamic.Location} {value : Dynamic.Value}
    (lookup : Dynamic.Environment.LooksUp environment binder.id location)
    (reads : Dynamic.Heap.Reads heap location {type := type, value := some value}) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap read.node.id value heap := by
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound read.found)
  · rw [read.form]
    exact .local (by rw [read.requirements, read.coercions]; rfl) lookup reads rfl rfl
  · rw [read.coercions]
    exact .nil

/-- `stored`'s body returns its parameter's word: its local mapping starts empty, `table[value] = value`
inserts the word at itself in place of the default, and the index read finds it. The local's context is a
binder extension of the body's. -/
theorem StoredBody.trace {source : TypedSource} (body : StoredBody source) {program : SourceSemantics.Program}
    {context localContext : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
    (before : Dynamic.Heap) (extension : BinderExtends source.owner context body.parts.table localContext)
    (word : Core.Word) :
    Dynamic.FunctionStatementsExecute program context evidence source (wordEnvironment body.parts.binder before)
      (wordHeap before word) [body.parts.declared.id, body.parts.assignment.id, body.parts.returned.id]
      localContext (.returned (.word word))
      (mappingHeap (wordHeap before word) (some (.mapping .word .word [(.word word, .word word)]))) := by
  let root : Dynamic.Location := ⟨(wordHeap before word).cells.length⟩
  let environment : Dynamic.Environment := (body.parts.table.id, root) :: wordEnvironment body.parts.binder before
  have parameterAllocation : Dynamic.Heap.Allocates before .word (some (.word word)) ⟨before.cells.length⟩
      (wordHeap before word) := .append
  have allocation : Dynamic.Heap.Allocates (wordHeap before word) (.mapping .word .word) none root
      (mappingHeap (wordHeap before word) none) := .append
  have stored : Dynamic.Heap.Allocates (wordHeap before word) (.mapping .word .word)
      (some (.mapping .word .word [(.word word, .word word)])) root
      (mappingHeap (wordHeap before word) (some (.mapping .word .word [(.word word, .word word)]))) := .append
  have parameterLookup : Dynamic.Environment.LooksUp environment body.parts.binder.id ⟨before.cells.length⟩ :=
    .tail body.tableDistinct .head
  have declared : Dynamic.StatementExecutes program context evidence source
      (wordEnvironment body.parts.binder before) (wordHeap before word) body.parts.declared.id localContext
      (.fallthrough environment) (mappingHeap (wordHeap before word) none) :=
    .letUninitialized (lookupStatement?_sound body.parts.declaredFound) body.parts.declaredForm
      (by rw [body.tableScheme]; rfl) extension (by rw [body.tableScheme]; exact allocation)
  have resolve : Dynamic.SourcePlaceResolves program localContext evidence source environment
      (mappingHeap (wordHeap before word) none) body.parts.resolution.target
      {location := root, rootType := .mapping .word .word, valueType := body.parts.resolution.target.type,
        projections := [.index (.word word)], selected := some (.word Core.Word.zero)}
      (mappingHeap (wordHeap before word) none) := by
    apply Dynamic.SourcePlaceResolves.intro (initialCell := {type := .mapping .word .word, value := none})
      (currentCell := {type := .mapping .word .word, value := none})
    · rw [body.parts.targetRoot]
      exact .head
    · exact allocation.reads_new
    · rw [body.parts.targetProjections]
      exact .index (local_value body.parts.keyRead evidence parameterLookup
        (allocation.preserves_read parameterAllocation.reads_new)) .nil
    · exact allocation.reads_new
    · exact .emptyMapping .word .word
    · exact .indexDefault .nil .word .nil
  have write : Dynamic.Heap.Writes (mappingHeap (wordHeap before word) none) root
      (some (.mapping .word .word [(.word word, .word word)]))
      (mappingHeap (wordHeap before word) (some (.mapping .word .word [(.word word, .word word)]))) :=
    .intro allocation.reads_new (write_last (wordHeap before word).cells _ _)
  have assigned : Dynamic.StatementExecutes program localContext evidence source environment
      (mappingHeap (wordHeap before word) none) body.parts.assignment.id localContext (.fallthrough environment)
      (mappingHeap (wordHeap before word) (some (.mapping .word .word [(.word word, .word word)]))) := by
    apply Dynamic.StatementExecutes.assignValue (updatedRoot := .mapping .word .word [(.word word, .word word)])
      (lookupStatement?_sound body.parts.assignmentFound) body.parts.assignmentForm
    refine .intro resolve (local_value body.parts.rightRead evidence parameterLookup
      (allocation.preserves_read parameterAllocation.reads_new)) ?_
    exact .intro allocation.reads_new rfl (.emptyMapping .word .word)
      (.indexDefault .nil .word (.leaf (.primitive (Dynamic.CompoundAssignmentApplies.plain_of_profile (.inl rfl))
        (.equal _ _))) (.append .nil)) write
  have indexed : Dynamic.ExpressionEvaluates program localContext evidence source environment
      (mappingHeap (wordHeap before word) (some (.mapping .word .word [(.word word, .word word)])))
      body.parts.index.id (.word word)
      (mappingHeap (wordHeap before word) (some (.mapping .word .word [(.word word, .word word)]))) := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound body.parts.indexFound)
    · rw [body.parts.indexForm]
      exact .indexFound (by rw [body.parts.indexRequirements, body.parts.indexCoercions]; rfl)
        (local_value body.parts.baseRead evidence .head stored.reads_new)
        (local_value body.parts.indexKey evidence parameterLookup (stored.preserves_read parameterAllocation.reads_new))
        (.head (.refl (.word word)))
    · rw [body.parts.indexCoercions]
      exact .nil
  exact .cons declared (.cons assigned (.singleton (lookupStatement?_sound body.parts.returnedFound)
    (by rw [body.parts.returnedForm]; intro id impossible; cases impossible)
    (.returnValue (lookupStatement?_sound body.parts.returnedFound) body.parts.returnedForm indexed)))

/-- A call of a builtin closure on one argument evaluates to the builtin's
result at the argument's value. -/
theorem builtin_value {source : TypedSource} {function : BuiltinFunctionId} {argument : ExpressionId}
    (call : Tests.SourceCoreBuiltinCalls.BuiltinCall source function argument) {program : SourceSemantics.Program}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {input result : Dynamic.Value}
    (argumentTrace : Dynamic.ExpressionEvaluates program context evidence source environment before argument input
      after)
    (applied : Dynamic.BuiltinApplies function [input] result) :
    Dynamic.ExpressionEvaluates program context evidence source environment before call.value.node.id result after := by
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound call.value.found)
  · rw [call.form, call.value.requirements, call.value.coercions]
    exact .builtinCall rfl (.cons argumentTrace .nil) (.builtin applied)
  · rw [call.value.coercions]
    exact .nil

/-- `summed`'s body returns the integer sum of its parameter's word with
itself: each call of `wordToInteger` gives the word's integer, and the call of
`integerAdd` their sum. -/
theorem SummedBody.trace {source : TypedSource} (body : SummedBody source) {program : SourceSemantics.Program}
    {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment) (before : Dynamic.Heap)
    (word : Core.Word) :
    Dynamic.FunctionStatementsExecute program context evidence source (wordEnvironment body.parts.binder before)
      (wordHeap before word) [body.parts.statement.id] context
      (.returned (.integer (Int.ofNat word.val + Int.ofNat word.val))) (wordHeap before word) := by
  have left := builtin_value (program := program) (context := context) body.parts.left
    (read_value body.parts.leftRead evidence before word) (.wordToInteger word)
  have right := builtin_value (program := program) (context := context) body.parts.right
    (read_value body.parts.rightRead evidence before word) (.wordToInteger word)
  have sum : Dynamic.ExpressionEvaluates program context evidence source (wordEnvironment body.parts.binder before)
      (wordHeap before word) body.parts.sum.node.id (.integer (Int.ofNat word.val + Int.ofNat word.val))
      (wordHeap before word) := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound body.parts.sum.found)
    · rw [body.parts.sumForm, body.parts.sum.requirements, body.parts.sum.coercions]
      exact .builtinCall rfl (.cons left (.cons right .nil)) (.builtin (.integerAdd _ _))
    · rw [body.parts.sum.coercions]
      exact .nil
  apply Dynamic.FunctionStatementsExecute.singleton (lookupStatement?_sound body.parts.statementFound)
  · intro expression impossible
    rw [body.parts.statementForm] at impossible
    cases impossible
  · exact .returnValue (lookupStatement?_sound body.parts.statementFound) body.parts.statementForm sum

/-- `zeroed`'s body returns the word 1 at a zero parameter and 0 at any other,
the opcode `iszero` on the parameter's word. -/
theorem ZeroedBody.trace {source : TypedSource} (body : ZeroedBody source) {program : SourceSemantics.Program}
    {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment) (before : Dynamic.Heap)
    (word : Core.Word) :
    Dynamic.FunctionStatementsExecute program context evidence source (wordEnvironment body.parts.binder before)
      (wordHeap before word) [body.parts.statement.id] context
      (.returned (.word (Dynamic.opcodeFlag (word == Core.Word.zero)))) (wordHeap before word) := by
  apply Dynamic.FunctionStatementsExecute.singleton (lookupStatement?_sound body.parts.statementFound)
  · intro expression impossible
    rw [body.parts.statementForm] at impossible
    cases impossible
  · exact .returnValue (lookupStatement?_sound body.parts.statementFound) body.parts.statementForm
      (builtin_value body.parts.tested (read_value body.parts.read evidence before word) (.wordOpcode rfl))

/-- `inverted`'s body returns the complement of the default word: its local
mapping starts empty, `table[value] ~=` complements the default at the
parameter's key and inserts the result there, and the index read finds it. The
local's context is a binder extension of the body's. -/
theorem InvertedBody.trace {source : TypedSource} (body : InvertedBody source) {program : SourceSemantics.Program}
    {context localContext : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
    (before : Dynamic.Heap) (extension : BinderExtends source.owner context body.parts.table localContext)
    (word : Core.Word) :
    Dynamic.FunctionStatementsExecute program context evidence source (wordEnvironment body.parts.binder before)
      (wordHeap before word) [body.parts.declared.id, body.parts.flip.id, body.parts.returned.id]
      localContext (.returned (.word Core.Word.zero.bitNot))
      (mappingHeap (wordHeap before word) (some (.mapping .word .word [(.word word, .word Core.Word.zero.bitNot)]))) := by
  let root : Dynamic.Location := ⟨(wordHeap before word).cells.length⟩
  let environment : Dynamic.Environment := (body.parts.table.id, root) :: wordEnvironment body.parts.binder before
  have parameterAllocation : Dynamic.Heap.Allocates before .word (some (.word word)) ⟨before.cells.length⟩
      (wordHeap before word) := .append
  have allocation : Dynamic.Heap.Allocates (wordHeap before word) (.mapping .word .word) none root
      (mappingHeap (wordHeap before word) none) := .append
  have flipped : Dynamic.Heap.Allocates (wordHeap before word) (.mapping .word .word)
      (some (.mapping .word .word [(.word word, .word Core.Word.zero.bitNot)])) root
      (mappingHeap (wordHeap before word) (some (.mapping .word .word [(.word word, .word Core.Word.zero.bitNot)]))) :=
    .append
  have parameterLookup : Dynamic.Environment.LooksUp environment body.parts.binder.id ⟨before.cells.length⟩ :=
    .tail body.tableDistinct .head
  have declared : Dynamic.StatementExecutes program context evidence source
      (wordEnvironment body.parts.binder before) (wordHeap before word) body.parts.declared.id localContext
      (.fallthrough environment) (mappingHeap (wordHeap before word) none) :=
    .letUninitialized (lookupStatement?_sound body.parts.declaredFound) body.parts.declaredForm
      (by rw [body.tableScheme]; rfl) extension (by rw [body.tableScheme]; exact allocation)
  have resolve : Dynamic.SourcePlaceResolves program localContext evidence source environment
      (mappingHeap (wordHeap before word) none) body.parts.resolution.target
      {location := root, rootType := .mapping .word .word, valueType := body.parts.resolution.target.type,
        projections := [.index (.word word)], selected := some (.word Core.Word.zero)}
      (mappingHeap (wordHeap before word) none) := by
    apply Dynamic.SourcePlaceResolves.intro (initialCell := {type := .mapping .word .word, value := none})
      (currentCell := {type := .mapping .word .word, value := none})
    · rw [body.parts.targetRoot]
      exact .head
    · exact allocation.reads_new
    · rw [body.parts.targetProjections]
      exact .index (local_value body.parts.keyRead evidence parameterLookup
        (allocation.preserves_read parameterAllocation.reads_new)) .nil
    · exact allocation.reads_new
    · exact .emptyMapping .word .word
    · exact .indexDefault .nil .word .nil
  have write : Dynamic.Heap.Writes (mappingHeap (wordHeap before word) none) root
      (some (.mapping .word .word [(.word word, .word Core.Word.zero.bitNot)]))
      (mappingHeap (wordHeap before word) (some (.mapping .word .word [(.word word, .word Core.Word.zero.bitNot)]))) :=
    .intro allocation.reads_new (write_last (wordHeap before word).cells _ _)
  have complemented : Dynamic.StatementExecutes program localContext evidence source environment
      (mappingHeap (wordHeap before word) none) body.parts.flip.id localContext (.fallthrough environment)
      (mappingHeap (wordHeap before word) (some (.mapping .word .word [(.word word, .word Core.Word.zero.bitNot)]))) := by
    apply Dynamic.StatementExecutes.assignBitNot
      (updatedRoot := .mapping .word .word [(.word word, .word Core.Word.zero.bitNot)])
      (lookupStatement?_sound body.parts.flipFound) body.parts.flipForm
    refine .intro resolve ?_
    exact .intro allocation.reads_new rfl (.emptyMapping .word .word)
      (.indexDefault .nil .word
        (.leaf (.primitive (fun type same => by rw [body.parts.targetType] at same; cases same)
          (.word Core.Word.zero))) (.append .nil)) write
  have indexed : Dynamic.ExpressionEvaluates program localContext evidence source environment
      (mappingHeap (wordHeap before word) (some (.mapping .word .word [(.word word, .word Core.Word.zero.bitNot)])))
      body.parts.index.id (.word Core.Word.zero.bitNot)
      (mappingHeap (wordHeap before word) (some (.mapping .word .word [(.word word, .word Core.Word.zero.bitNot)]))) := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound body.parts.indexFound)
    · rw [body.parts.indexForm]
      exact .indexFound (by rw [body.parts.indexRequirements, body.parts.indexCoercions]; rfl)
        (local_value body.parts.baseRead evidence .head flipped.reads_new)
        (local_value body.parts.indexKey evidence parameterLookup (flipped.preserves_read parameterAllocation.reads_new))
        (.head (.refl (.word word)))
    · rw [body.parts.indexCoercions]
      exact .nil
  exact .cons declared (.cons complemented (.singleton (lookupStatement?_sound body.parts.returnedFound)
    (by rw [body.parts.returnedForm]; intro id impossible; cases impossible)
    (.returnValue (lookupStatement?_sound body.parts.returnedFound) body.parts.returnedForm indexed)))

/-- `broken`'s body returns its parameter: the loop's condition is `true`, its
body breaks at once, and the loop falls through at the loop's own bindings. -/
theorem BrokenBody.trace {source : TypedSource} (body : BrokenBody source) {program : SourceSemantics.Program}
    {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment) (before : Dynamic.Heap)
    (word : Core.Word) :
    Dynamic.FunctionStatementsExecute program context evidence source (wordEnvironment body.parts.binder before)
      (wordHeap before word) [body.parts.loop.id, body.parts.returned.id] context (.returned (.word word))
      (wordHeap before word) := by
  have parameterAllocation : Dynamic.Heap.Allocates before .word (some (.word word)) ⟨before.cells.length⟩
      (wordHeap before word) := .append
  have tested : Dynamic.ExpressionEvaluates program context evidence source (wordEnvironment body.parts.binder before)
      (wordHeap before word) body.parts.condition.id (.bool true) (wordHeap before word) := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound body.parts.conditionFound)
    · rw [body.parts.conditionForm]
      exact .builtinBoolean (by rw [body.parts.conditionRequirements, body.parts.conditionCoercions]; rfl)
    · rw [body.parts.conditionCoercions]
      exact .nil
  have broke : Dynamic.StatementsExecute program context evidence source (wordEnvironment body.parts.binder before)
      (wordHeap before word) [body.parts.jump.id] context (.breaking (wordEnvironment body.parts.binder before))
      (wordHeap before word) :=
    .terminal (.breakStmt (lookupStatement?_sound body.parts.jumpFound) body.parts.jumpForm) (.breaking _)
  have looped : Dynamic.StatementExecutes program context evidence source (wordEnvironment body.parts.binder before)
      (wordHeap before word) body.parts.loop.id context (.fallthrough (wordEnvironment body.parts.binder before))
      (wordHeap before word) :=
    .whileLoop (lookupStatement?_sound body.parts.loopFound) body.parts.loopForm (.breaks tested broke)
  exact .cons looped (.singleton (lookupStatement?_sound body.parts.returnedFound)
    (by rw [body.parts.returnedForm]; intro id impossible; cases impossible)
    (.returnValue (lookupStatement?_sound body.parts.returnedFound) body.parts.returnedForm
      (local_value body.parts.read evidence .head parameterAllocation.reads_new)))

/-- `counted`'s body returns its parameter: the header declares `go` at
`true`, the first test reads it, the body continues, the post header assigns
`go` its `false`, and the second test ends the loop, which falls through at the
loop's own bindings. The local's context is a binder extension of the body's. -/
theorem CountedBody.trace {source : TypedSource} (body : CountedBody source) {program : SourceSemantics.Program}
    {context loopContext : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment) (before : Dynamic.Heap)
    (extension : BinderExtends source.owner context body.parts.go loopContext) (word : Core.Word) :
    Dynamic.FunctionStatementsExecute program context evidence source (wordEnvironment body.parts.binder before)
      (wordHeap before word) [body.parts.loop.id, body.parts.returned.id] context (.returned (.word word))
      (boolHeap (wordHeap before word) false) := by
  let flag : Dynamic.Location := ⟨(wordHeap before word).cells.length⟩
  let environment : Dynamic.Environment := (body.parts.go.id, flag) :: wordEnvironment body.parts.binder before
  have parameterAllocation : Dynamic.Heap.Allocates before .word (some (.word word)) ⟨before.cells.length⟩
      (wordHeap before word) := .append
  have raised : Dynamic.Heap.Allocates (wordHeap before word) .bool (some (.bool true)) flag
      (boolHeap (wordHeap before word) true) := .append
  have lowered : Dynamic.Heap.Allocates (wordHeap before word) .bool (some (.bool false)) flag
      (boolHeap (wordHeap before word) false) := .append
  have started : Dynamic.ExpressionEvaluates program context evidence source (wordEnvironment body.parts.binder before)
      (wordHeap before word) body.parts.start.id (.bool true) (wordHeap before word) := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound body.parts.startFound)
    · rw [body.parts.startForm]
      exact .builtinBoolean (by rw [body.parts.startRequirements, body.parts.startCoercions]; rfl)
    · rw [body.parts.startCoercions]
      exact .nil
  have initialized : Dynamic.ForItemsExecute program context evidence source (wordEnvironment body.parts.binder before)
      (wordHeap before word) [.letDecl body.parts.go (some body.parts.start.id)] loopContext environment
      (boolHeap (wordHeap before word) true) :=
    .cons (.letInitialized started (by rw [body.goScheme]; rfl) extension (by rw [body.goScheme]; exact raised)) .nil
  have stopped : Dynamic.ExpressionEvaluates program loopContext evidence source environment
      (boolHeap (wordHeap before word) true) body.parts.stop.id (.bool false) (boolHeap (wordHeap before word) true) := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound body.parts.stopFound)
    · rw [body.parts.stopForm]
      exact .builtinBoolean (by rw [body.parts.stopRequirements, body.parts.stopCoercions]; rfl)
    · rw [body.parts.stopCoercions]
      exact .nil
  have continued : Dynamic.StatementsExecute program loopContext evidence source environment
      (boolHeap (wordHeap before word) true) [body.parts.jump.id] loopContext (.continuing environment)
      (boolHeap (wordHeap before word) true) :=
    .terminal (.continueStmt (lookupStatement?_sound body.parts.jumpFound) body.parts.jumpForm) (.continuing _)
  have resolve : Dynamic.SourcePlaceResolves program loopContext evidence source environment
      (boolHeap (wordHeap before word) true) body.parts.resolution.target
      {location := flag, rootType := .bool, valueType := body.parts.resolution.target.type,
        projections := [], selected := some (.bool true)}
      (boolHeap (wordHeap before word) true) := by
    apply Dynamic.SourcePlaceResolves.intro (initialCell := {type := .bool, value := some (.bool true)})
      (currentCell := {type := .bool, value := some (.bool true)})
    · rw [body.parts.targetRoot]
      exact .head
    · exact raised.reads_new
    · rw [body.parts.targetProjections]
      exact .nil
    · exact raised.reads_new
    · exact .initialized
    · exact .nil
  have write : Dynamic.Heap.Writes (boolHeap (wordHeap before word) true) flag (some (.bool false))
      (boolHeap (wordHeap before word) false) :=
    .intro raised.reads_new (write_last (wordHeap before word).cells _ _)
  have posted : Dynamic.ForItemsExecute program loopContext evidence source environment
      (boolHeap (wordHeap before word) true) [.assignValue body.parts.resolution .equal body.parts.stop.id]
      loopContext environment (boolHeap (wordHeap before word) false) := by
    refine .cons (.assignValue (updatedRoot := .bool false) ?_) .nil
    refine .intro resolve stopped ?_
    exact .intro raised.reads_new rfl .initialized
      (.leaf (.primitive (Dynamic.CompoundAssignmentApplies.plain_of_profile (.inl rfl)) (.equal _ _))) write
  have iterated : Dynamic.ForLoopExecutes program loopContext evidence source environment
      (boolHeap (wordHeap before word) true) body.parts.test.node.id
      [.assignValue body.parts.resolution .equal body.parts.stop.id] [body.parts.jump.id] loopContext
      (.fallthrough environment) (boolHeap (wordHeap before word) false) :=
    .nextContinue (local_value body.parts.test evidence .head raised.reads_new) continued posted
      (.done (local_value body.parts.test evidence .head lowered.reads_new))
  have looped : Dynamic.StatementExecutes program context evidence source (wordEnvironment body.parts.binder before)
      (wordHeap before word) body.parts.loop.id context (.fallthrough (wordEnvironment body.parts.binder before))
      (boolHeap (wordHeap before word) false) :=
    .forLoop (lookupStatement?_sound body.parts.loopFound) body.parts.loopForm initialized iterated
  exact .cons looped (.singleton (lookupStatement?_sound body.parts.returnedFound)
    (by rw [body.parts.returnedForm]; intro id impossible; cases impossible)
    (.returnValue (lookupStatement?_sound body.parts.returnedFound) body.parts.returnedForm
      (local_value body.parts.read evidence .head (lowered.preserves_read parameterAllocation.reads_new))))

/-- `tripled`'s body returns the triple of its parameter's word, packed as a
product of the first element and the pair of the others. -/
theorem TripledBody.trace {source : TypedSource} (body : TripledBody source) {program : SourceSemantics.Program}
    {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment) (before : Dynamic.Heap)
    (word : Core.Word) :
    Dynamic.FunctionStatementsExecute program context evidence source (wordEnvironment body.parts.binder before)
      (wordHeap before word) [body.parts.statement.id] context
      (.returned (.product (.word word) (.product (.word word) (.word word)))) (wordHeap before word) := by
  have packed : Dynamic.ExpressionEvaluates program context evidence source (wordEnvironment body.parts.binder before)
      (wordHeap before word) body.parts.tuple.id (.product (.word word) (.product (.word word) (.word word)))
      (wordHeap before word) := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound body.parts.tupleFound)
    · rw [body.parts.tupleForm]
      exact .tuple (by rw [body.parts.tupleRequirements, body.parts.tupleCoercions]; rfl)
        (.cons (read_value body.parts.first evidence before word)
          (.cons (read_value body.parts.second evidence before word)
            (.cons (read_value body.parts.third evidence before word) .nil)))
        (.cons (.cons (.singleton _)))
    · rw [body.parts.tupleCoercions]
      exact .nil
  apply Dynamic.FunctionStatementsExecute.singleton (lookupStatement?_sound body.parts.statementFound)
  · intro expression impossible
    rw [body.parts.statementForm] at impossible
    cases impossible
  · exact .returnValue (lookupStatement?_sound body.parts.statementFound) body.parts.statementForm packed

/-- `boxed`'s body returns `Item` applied to its parameter's word, at valid
constructor metadata. -/
theorem BoxedBody.trace {source : TypedSource} (body : BoxedBody source) {program : SourceSemantics.Program}
    {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment) (before : Dynamic.Heap)
    (valid : DataConstructorInstantiation.Valid context body.parts.instantiation) (word : Core.Word) :
    Dynamic.FunctionStatementsExecute program context evidence source (wordEnvironment body.parts.binder before)
      (wordHeap before word) [body.parts.statement.id] context
      (.returned (.constructed body.parts.instantiation [.word word])) (wordHeap before word) := by
  have constructed : Dynamic.ExpressionEvaluates program context evidence source
      (wordEnvironment body.parts.binder before) (wordHeap before word) body.parts.construct.id
      (.constructed body.parts.instantiation [.word word]) (wordHeap before word) := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound body.parts.constructFound)
    · rw [body.parts.constructForm]
      exact .constructor (by rw [body.parts.constructRequirements, body.parts.constructCoercions]; rfl) valid
        (.cons (read_value body.parts.read evidence before word) .nil)
    · rw [body.parts.constructCoercions]
      exact .nil
  apply Dynamic.FunctionStatementsExecute.singleton (lookupStatement?_sound body.parts.statementFound)
  · intro expression impossible
    rw [body.parts.statementForm] at impossible
    cases impossible
  · exact .returnValue (lookupStatement?_sound body.parts.statementFound) body.parts.statementForm constructed

end Tests.SourceCoreAcceptedOneCall
end

section
/-! The accepted-body public theorems at the call root. Runtime checks place
every expression node of the twenty-three rows among the nested sites or their callees
and each statement list in the supported shape; the complete inventory turns
them into the rows of a family and gives the admitted callee's static
receipts. The original Source executions of `relay`, `twice`, `tailed`, `stored`, `summed`, `zeroed`,
`inverted`, `broken`, `counted`, `tripled`, `narrow` and `roundTrip`, whose calls run `identity`'s body instance, are lifted through the checked
shapes, and with the existing start receipts the call root's theorems apply at
the first public call of each in both directions; `stored`'s and `inverted`'s executions end in their
local's context (`accepted_call_with_locals`), and `summed`'s and `tripled`'s return an integer and a
triple (`accepted_call_returning`). The call root's reflection
needs no Source execution (`accepted_reflection`). At a faulting word the
row's original Source fault is lifted to a staged fault trace, given that the
direct calls of the row and of `identity` have plain callees, and the call
root's failure theorem applies (`accepted_failure`). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreAcceptedOneCall
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreAcceptedFixture
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)

variable {fixture : CompiledFixture workspace options} {whole : WholeInventory fixture} {row : Row fixture}

private theorem mono_signatures {owner : Resolved.DeclarationId} {context final : SourceSemantics.Context}
    {binders : List TypedBinder} {types : List TypeSystem.Ty}
    (extension : MonoBindersExtend owner context binders types final) : final.signatures = context.signatures := by
  induction extension with
  | nil => rfl
  | cons _ head _ ih => exact ih.trans head.context_fields.1

/-- A header's lexical context has the program's signatures. -/
theorem header_signatures
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)) :
    header.context.signatures = fixture.recipe.compiled.sourceProgram.signatures := by
  rw [mono_signatures header.extended, header.frame.context]
  cases header.frame.instantiated with
  | intro _ _ _ _ _ _ _ contextEq =>
    rw [contextEq]
    rfl

/-- A row whose only parameter is a `Word` has the header parameter types
`[.word]`, and its header allocates that parameter in the next cell. -/
theorem word_parameter (selected : SelectedInventory whole row) {binder : TypedBinder}
    (inputs : row.original.function.typedBody.inputs = [binder]) (scheme : binder.scheme = .mono .word)
    (before : Dynamic.Heap) (word : Core.Word) :
    selected.packet.header.types = [.word] ∧
    Dynamic.BindersAllocate [] before selected.packet.header.function.parameters [.word word]
      (wordEnvironment binder before) (wordHeap before word) := by
  have sourceInputs : selected.packet.header.function.source.inputs = [binder] := by
    rw [selected.source_eq]
    exact inputs
  have parameters : selected.packet.header.function.parameters = [binder] :=
    selected.packet.header.parameters.trans (selected.packet.header.inputs.symm.trans sourceInputs)
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq selected.packet.header.extended
  have allocation : Dynamic.Heap.Allocates before .word (some (.word word)) ⟨before.cells.length⟩
      (wordHeap before word) := .append
  refine ⟨?_, ?_⟩
  · simpa only [parameters, List.map_cons, List.map_nil, scheme, TypeSystem.Scheme.mono] using types.symm
  · rw [parameters]
    exact .cons (by simpa only [scheme, TypeSystem.Scheme.mono] using allocation) (.nil _ _)

/-- `identity`'s global application at the empty dictionary, at any heap: its
header's Source body runs on its parameter in the next cell and returns it. -/
theorem identity_applies {identity : Row fixture} (identitySelected : SelectedInventory whole identity)
    {called : DeclarationInstantiation → Prop}
    (calls : CallRows fixture called fixture.recipe.compiled.indexed.base.functions)
    (identityBody : IdentityBody identity.original.function.typedBody) {instantiation : DeclarationInstantiation}
    (selects : instantiation = CallableNamedCanonicalOrder.retainedInstantiation identity.original)
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (before : Dynamic.Heap)
    (word : Core.Word) :
    Dynamic.CallableApplies (Program.ofChecked fixture.recipe.compiled.sourceProgram) context evidence [] before
      (.global ⟨instantiation, []⟩) [.word word] (.word word) (wordHeap before word) := by
  have calleeSource : identitySelected.packet.header.sourceBody.source = identity.original.function.typedBody :=
    identitySelected.packet.header.frame.source.symm.trans identitySelected.source_eq
  have covers : Dynamic.EvidenceEnvironment.Covers identitySelected.packet.header.sourceBody.context [] := by
    have frameCovers := identitySelected.packet.header.frame.covers
    rw [calls.header_evidence identitySelected.packet] at frameCovers
    exact frameCovers
  have extended := identitySelected.packet.header.extended
  rw [identitySelected.packet.header.frame.parameters, identitySelected.packet.header.frame.source,
    identitySelected.packet.header.frame.context] at extended
  have rootsEq : Dynamic.StatementRoots identitySelected.packet.header.sourceBody.source.roots
      [identityBody.statement.id] := by
    rw [calleeSource, identityBody.roots]
    exact .cons .nil
  have allocation : Dynamic.Heap.Allocates before .word (some (.word word)) ⟨before.cells.length⟩
      (wordHeap before word) := .append
  have allocated : Dynamic.BindersAllocate [] before identitySelected.packet.header.sourceBody.source.inputs
      [.word word] (wordEnvironment identityBody.binder before) (wordHeap before word) := by
    rw [calleeSource, identityBody.inputs]
    exact .cons (by simpa only [identityBody.binderScheme, TypeSystem.Scheme.mono] using allocation) (.nil _ _)
  have execute : Dynamic.FunctionStatementsExecute (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      identitySelected.packet.header.context [] identitySelected.packet.header.sourceBody.source
      (wordEnvironment identityBody.binder before) (wordHeap before word) [identityBody.statement.id]
      identitySelected.packet.header.context (.returned (.word word)) (wordHeap before word) := by
    rw [calleeSource]
    exact identityBody.trace [] before word
  have instantiates := identitySelected.packet.header.frame.instantiated
  rw [identitySelected.packet.aligned.metadata, identitySelected.original, ← selects] at instantiates
  exact .global instantiates rfl covers (.returned covers rootsEq extended allocated execute rfl)

/-- The statement roots of a header whose row's body is one statement. -/
private theorem single_body (selected : SelectedInventory whole row) {statement : StatementId}
    (roots : row.original.function.typedBody.roots = [.statement statement]) :
    selected.packet.header.function.body = [statement] := by
  have headerRoots : selected.packet.header.function.source.roots = [statement].map NodeId.statement := by
    rw [selected.source_eq]
    exact roots
  exact statementRoots_injective (selected.packet.header.agreement.roots.symm.trans headerRoots)

/-- The statement roots of a header whose row's body is three statements. -/
private theorem three_body (selected : SelectedInventory whole row) {first second third : StatementId}
    (roots : row.original.function.typedBody.roots = [.statement first, .statement second, .statement third]) :
    selected.packet.header.function.body = [first, second, third] := by
  have headerRoots : selected.packet.header.function.source.roots = [first, second, third].map NodeId.statement := by
    rw [selected.source_eq]
    exact roots
  exact statementRoots_injective (selected.packet.header.agreement.roots.symm.trans headerRoots)

/-- The statement roots of a header whose row's body is two statements. -/
private theorem two_body (selected : SelectedInventory whole row) {first second : StatementId}
    (roots : row.original.function.typedBody.roots = [.statement first, .statement second]) :
    selected.packet.header.function.body = [first, second] := by
  have headerRoots : selected.packet.header.function.source.roots = [first, second].map NodeId.statement := by
    rw [selected.source_eq]
    exact roots
  exact statementRoots_injective (selected.packet.header.agreement.roots.symm.trans headerRoots)

/-- The original Source execution of `relay`'s body at its header: the direct
call's global application runs `identity`'s body instance, its header's Source
body, at the empty dictionary. -/
theorem relay_source (selected : SelectedInventory whole row) {identity : Row fixture}
    (identitySelected : SelectedInventory whole identity) {called : DeclarationInstantiation → Prop}
    (calls : CallRows fixture called fixture.recipe.compiled.indexed.base.functions)
    (identityBody : IdentityBody identity.original.function.typedBody)
    (relayBody : RelayBody fixture (CallableNamedCanonicalOrder.retainedInstantiation identity.original)
      row.original.function.typedBody)
    (word : Core.Word) :
    Dynamic.FunctionStatementsExecute (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      selected.packet.header.context selected.packet.header.function.evidence selected.packet.header.function.source
      (wordEnvironment relayBody.binder ⟨[]⟩) (wordHeap ⟨[]⟩ word) selected.packet.header.function.body
      selected.packet.header.context (.returned (.word word)) (wordHeap (wordHeap ⟨[]⟩ word) word) := by
  have member : relayBody.identity ∈ selected.packet.header.context.signatures.functions := by
    rw [header_signatures selected.packet.header]
    exact relayBody.member
  rw [single_body selected relayBody.roots, selected.source_eq]
  exact relayBody.trace selected.packet.header.function.evidence ⟨[]⟩ word
    (call_valid relayBody.call member)
    (identity_applies identitySelected calls identityBody relayBody.selects selected.packet.header.context
      selected.packet.header.function.evidence (wordHeap ⟨[]⟩ word) word)

/-- The original Source execution of `twice`'s body at its header: the inner
call's result is the outer call's argument, and each call's global application
runs `identity`'s body instance at the empty dictionary. -/
theorem twice_source (selected : SelectedInventory whole row) {identity : Row fixture}
    (identitySelected : SelectedInventory whole identity) {called : DeclarationInstantiation → Prop}
    (calls : CallRows fixture called fixture.recipe.compiled.indexed.base.functions)
    (identityBody : IdentityBody identity.original.function.typedBody)
    (twiceBody : TwiceBody fixture (CallableNamedCanonicalOrder.retainedInstantiation identity.original)
      row.original.function.typedBody)
    (word : Core.Word) :
    Dynamic.FunctionStatementsExecute (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      selected.packet.header.context selected.packet.header.function.evidence selected.packet.header.function.source
      (wordEnvironment twiceBody.parts.binder ⟨[]⟩) (wordHeap ⟨[]⟩ word) selected.packet.header.function.body
      selected.packet.header.context (.returned (.word word)) (wordHeap (wordHeap (wordHeap ⟨[]⟩ word) word) word) := by
  have member : twiceBody.identity ∈ selected.packet.header.context.signatures.functions := by
    rw [header_signatures selected.packet.header]
    exact twiceBody.member
  rw [single_body selected twiceBody.parts.roots, selected.source_eq]
  exact twiceBody.trace selected.packet.header.function.evidence ⟨[]⟩ word
    (call_valid twiceBody.parts.inner member) (call_valid twiceBody.parts.outer member)
    (identity_applies identitySelected calls identityBody twiceBody.innerSelects selected.packet.header.context
      selected.packet.header.function.evidence (wordHeap ⟨[]⟩ word) word)
    (identity_applies identitySelected calls identityBody twiceBody.outerSelects selected.packet.header.context
      selected.packet.header.function.evidence (wordHeap (wordHeap ⟨[]⟩ word) word) word)

/-- The original Source execution of `tailed`'s body at its header: its final
value is the direct call's, whose global application runs `identity`'s body
instance, its header's Source body, at the empty dictionary. -/
theorem tailed_source (selected : SelectedInventory whole row) {identity : Row fixture}
    (identitySelected : SelectedInventory whole identity) {called : DeclarationInstantiation → Prop}
    (calls : CallRows fixture called fixture.recipe.compiled.indexed.base.functions)
    (identityBody : IdentityBody identity.original.function.typedBody)
    (tailedBody : TailedBody fixture (CallableNamedCanonicalOrder.retainedInstantiation identity.original)
      row.original.function.typedBody)
    (word : Core.Word) :
    Dynamic.FunctionStatementsExecute (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      selected.packet.header.context selected.packet.header.function.evidence selected.packet.header.function.source
      (wordEnvironment tailedBody.binder ⟨[]⟩) (wordHeap ⟨[]⟩ word) selected.packet.header.function.body
      selected.packet.header.context (.returned (.word word)) (wordHeap (wordHeap ⟨[]⟩ word) word) := by
  have member : tailedBody.identity ∈ selected.packet.header.context.signatures.functions := by
    rw [header_signatures selected.packet.header]
    exact tailedBody.member
  rw [single_body selected tailedBody.roots, selected.source_eq]
  exact tailedBody.trace selected.packet.header.function.evidence ⟨[]⟩ word
    (call_valid tailedBody.call member)
    (identity_applies identitySelected calls identityBody tailedBody.selects selected.packet.header.context
      selected.packet.header.function.evidence (wordHeap ⟨[]⟩ word) word)

/-- The original Source execution of `narrow`'s body at its header, at a word
canonical for `uint8`. -/
theorem narrow_source (selected : SelectedInventory whole row) (narrowBody : NarrowBody row.original.function.typedBody)
    (word : Core.Word) (canonical : TypeSystem.FixedInteger.canonical ⟨false, .w8⟩ word.val = true) :
    Dynamic.FunctionStatementsExecute (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      selected.packet.header.context selected.packet.header.function.evidence selected.packet.header.function.source
      (wordEnvironment narrowBody.parts.binder ⟨[]⟩) (wordHeap ⟨[]⟩ word) selected.packet.header.function.body
      selected.packet.header.context (.returned (.word word)) (wordHeap ⟨[]⟩ word) := by
  rw [single_body selected narrowBody.parts.roots, selected.source_eq]
  exact narrowBody.trace selected.packet.header.function.evidence ⟨[]⟩ word canonical

/-- The original Source execution of `roundTrip`'s body at its header, at a
word canonical for `uint8`. -/
theorem roundTrip_source (selected : SelectedInventory whole row)
    (roundTripBody : RoundTripBody row.original.function.typedBody)
    (word : Core.Word) (canonical : TypeSystem.FixedInteger.canonical ⟨false, .w8⟩ word.val = true) :
    Dynamic.FunctionStatementsExecute (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      selected.packet.header.context selected.packet.header.function.evidence selected.packet.header.function.source
      (wordEnvironment roundTripBody.parts.binder ⟨[]⟩) (wordHeap ⟨[]⟩ word) selected.packet.header.function.body
      selected.packet.header.context (.returned (.word word)) (wordHeap ⟨[]⟩ word) := by
  rw [single_body selected roundTripBody.parts.roots, selected.source_eq]
  exact roundTripBody.trace selected.packet.header.function.evidence ⟨[]⟩ word canonical

/-- The original Source execution of `narrow`'s body at its header faults with
the dirty-integer reason at a word not canonical for `uint8`. -/
theorem narrow_fault (selected : SelectedInventory whole row) (narrowBody : NarrowBody row.original.function.typedBody)
    (word : Core.Word) (dirty : TypeSystem.FixedInteger.canonical ⟨false, .w8⟩ word.val = false) :
    Dynamic.FunctionStatementsFault (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      selected.packet.header.context selected.packet.header.function.evidence selected.packet.header.function.source
      (wordEnvironment narrowBody.parts.binder ⟨[]⟩) (wordHeap ⟨[]⟩ word) selected.packet.header.function.body
      selected.packet.header.context .dirtyHigherBitsForInteger (wordHeap ⟨[]⟩ word) := by
  rw [single_body selected narrowBody.parts.roots, selected.source_eq]
  exact narrowBody.fault selected.packet.header.function.evidence ⟨[]⟩ word dirty

/-- The original Source execution at its header of a three-statement body that
first initializes a `uint8` local with the conversion of its `Word` parameter,
as `doubled`'s, `shifted`'s and `flipped`'s do, faults there with the
dirty-integer reason at a word not canonical for `uint8`. -/
theorem initializer_fault (selected : SelectedInventory whole row) {binder target : TypedBinder}
    (read : Tests.SourceCoreNamedBranch.Read row.original.function.typedBody binder .word)
    (converted : Tests.SourceCoreBuiltinCalls.BuiltinCall row.original.function.typedBody
      (.fixedFromWord ⟨false, .w8⟩) read.node.id)
    {initialized assignment returned : StatementNode}
    (roots : row.original.function.typedBody.roots =
      [.statement initialized.id, .statement assignment.id, .statement returned.id])
    (found : row.original.function.typedBody.lookupStatement? initialized.id = some initialized)
    (form : initialized.form = .letDecl target (some converted.value.node.id))
    (scheme : target.scheme = .mono (.fixed ⟨false, .w8⟩))
    (word : Core.Word) (dirty : TypeSystem.FixedInteger.canonical ⟨false, .w8⟩ word.val = false) :
    Dynamic.FunctionStatementsFault (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      selected.packet.header.context selected.packet.header.function.evidence selected.packet.header.function.source
      (wordEnvironment binder ⟨[]⟩) (wordHeap ⟨[]⟩ word) selected.packet.header.function.body
      selected.packet.header.context .dirtyHigherBitsForInteger (wordHeap ⟨[]⟩ word) := by
  rw [three_body selected roots, selected.source_eq]
  exact dirty_initializer read converted found form scheme selected.packet.header.function.evidence ⟨[]⟩ word dirty
    assignment.id [returned.id]

/-- The original Source execution of `doubled`'s body at its header panics
with `0x11` at a word canonical for `uint8` whose double is outside `uint8`.
The local's binder extension comes from the header's typing certificate. -/
theorem doubled_panic (selected : SelectedInventory whole row)
    (doubledBody : DoubledBody row.original.function.typedBody)
    (certified : SelectedCompilationNamedSourceTyping.Certified selected.packet.header) (word : Core.Word)
    (canonical : TypeSystem.FixedInteger.canonical ⟨false, .w8⟩ word.val = true)
    (outside : ¬ Dynamic.FixedInRange ⟨false, .w8⟩
      (Dynamic.checkedResult .add (Dynamic.fixedValue ⟨false, .w8⟩ word) (Dynamic.fixedValue ⟨false, .w8⟩ word))) :
    ∃ finalContext, Dynamic.FunctionStatementsFault (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      selected.packet.header.context selected.packet.header.function.evidence selected.packet.header.function.source
      (wordEnvironment doubledBody.parts.binder ⟨[]⟩) (wordHeap ⟨[]⟩ word) selected.packet.header.function.body
      finalContext (.panic 0x11) (byteHeap (wordHeap ⟨[]⟩ word) word) := by
  have body := three_body selected doubledBody.parts.roots
  have unique : NodeOccurrencesUnique row.original.function.typedBody :=
    selected.source_eq ▸ selected.packet.header.unique
  obtain ⟨_final, _facts, typed, _completes⟩ := certified.statements
  rw [body, selected.source_eq] at typed
  cases typed with
  | cons head _ =>
    obtain ⟨node, contains, formTyped⟩ := Dynamic.StatementHasType.formTyping head
    cases Option.some.inj ((lookupStatement?_complete unique contains).symm.trans doubledBody.parts.initializedFound)
    rw [doubledBody.parts.initializedForm] at formTyped
    cases formTyped with
    | letInitialized _ _ extension =>
      rw [body, selected.source_eq]
      exact ⟨_, doubledBody.panic selected.packet.header.function.evidence ⟨[]⟩ extension word canonical outside⟩
    | letInitializedGeneralized polymorphic =>
      rw [doubledBody.targetScheme] at polymorphic
      exact absurd rfl polymorphic

/-- The original Source execution of `stored`'s body at its header returns its
parameter's word, which its index read finds where the assignment through the
same index put it. The local's binder extension comes from the header's typing
certificate. -/
theorem stored_source (selected : SelectedInventory whole row) (storedBody : StoredBody row.original.function.typedBody)
    (certified : SelectedCompilationNamedSourceTyping.Certified selected.packet.header) (word : Core.Word) :
    ∃ finalContext, Dynamic.FunctionStatementsExecute (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      selected.packet.header.context selected.packet.header.function.evidence selected.packet.header.function.source
      (wordEnvironment storedBody.parts.binder ⟨[]⟩) (wordHeap ⟨[]⟩ word) selected.packet.header.function.body
      finalContext (.returned (.word word))
      (mappingHeap (wordHeap ⟨[]⟩ word) (some (.mapping .word .word [(.word word, .word word)]))) := by
  have body := three_body selected storedBody.parts.roots
  have unique : NodeOccurrencesUnique row.original.function.typedBody :=
    selected.source_eq ▸ selected.packet.header.unique
  obtain ⟨_final, _facts, typed, _completes⟩ := certified.statements
  rw [body, selected.source_eq] at typed
  cases typed with
  | cons head _ =>
    obtain ⟨node, contains, formTyped⟩ := Dynamic.StatementHasType.formTyping head
    cases Option.some.inj ((lookupStatement?_complete unique contains).symm.trans storedBody.parts.declaredFound)
    rw [storedBody.parts.declaredForm] at formTyped
    cases formTyped with
    | letUninitialized _ extension =>
      rw [body, selected.source_eq]
      exact ⟨_, storedBody.trace selected.packet.header.function.evidence ⟨[]⟩ extension word⟩

/-- The original Source execution of `summed`'s body at its header returns the
integer sum of its parameter's word with itself. -/
theorem summed_source (selected : SelectedInventory whole row) (summedBody : SummedBody row.original.function.typedBody)
    (word : Core.Word) :
    Dynamic.FunctionStatementsExecute (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      selected.packet.header.context selected.packet.header.function.evidence selected.packet.header.function.source
      (wordEnvironment summedBody.parts.binder ⟨[]⟩) (wordHeap ⟨[]⟩ word) selected.packet.header.function.body
      selected.packet.header.context (.returned (.integer (Int.ofNat word.val + Int.ofNat word.val)))
      (wordHeap ⟨[]⟩ word) := by
  rw [single_body selected summedBody.parts.roots, selected.source_eq]
  exact summedBody.trace selected.packet.header.function.evidence ⟨[]⟩ word

/-- The original Source execution of `zeroed`'s body at its header returns the
opcode `iszero` on its parameter's word. -/
theorem zeroed_source (selected : SelectedInventory whole row) (zeroedBody : ZeroedBody row.original.function.typedBody)
    (word : Core.Word) :
    Dynamic.FunctionStatementsExecute (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      selected.packet.header.context selected.packet.header.function.evidence selected.packet.header.function.source
      (wordEnvironment zeroedBody.parts.binder ⟨[]⟩) (wordHeap ⟨[]⟩ word) selected.packet.header.function.body
      selected.packet.header.context (.returned (.word (Dynamic.opcodeFlag (word == Core.Word.zero))))
      (wordHeap ⟨[]⟩ word) := by
  rw [single_body selected zeroedBody.parts.roots, selected.source_eq]
  exact zeroedBody.trace selected.packet.header.function.evidence ⟨[]⟩ word

/-- The original Source execution of `inverted`'s body at its header returns
the complement of the default word, which its index read finds where the
in-place `~` through the same index put it. The local's binder extension comes
from the header's typing certificate. -/
theorem inverted_source (selected : SelectedInventory whole row)
    (invertedBody : InvertedBody row.original.function.typedBody)
    (certified : SelectedCompilationNamedSourceTyping.Certified selected.packet.header) (word : Core.Word) :
    ∃ finalContext, Dynamic.FunctionStatementsExecute (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      selected.packet.header.context selected.packet.header.function.evidence selected.packet.header.function.source
      (wordEnvironment invertedBody.parts.binder ⟨[]⟩) (wordHeap ⟨[]⟩ word) selected.packet.header.function.body
      finalContext (.returned (.word Core.Word.zero.bitNot))
      (mappingHeap (wordHeap ⟨[]⟩ word) (some (.mapping .word .word [(.word word, .word Core.Word.zero.bitNot)]))) := by
  have body := three_body selected invertedBody.parts.roots
  have unique : NodeOccurrencesUnique row.original.function.typedBody :=
    selected.source_eq ▸ selected.packet.header.unique
  obtain ⟨_final, _facts, typed, _completes⟩ := certified.statements
  rw [body, selected.source_eq] at typed
  cases typed with
  | cons head _ =>
    obtain ⟨node, contains, formTyped⟩ := Dynamic.StatementHasType.formTyping head
    cases Option.some.inj ((lookupStatement?_complete unique contains).symm.trans invertedBody.parts.declaredFound)
    rw [invertedBody.parts.declaredForm] at formTyped
    cases formTyped with
    | letUninitialized _ extension =>
      rw [body, selected.source_eq]
      exact ⟨_, invertedBody.trace selected.packet.header.function.evidence ⟨[]⟩ extension word⟩

/-- The original Source execution of `broken`'s body at its header returns its
parameter after its `while (true)` loop breaks at once. -/
theorem broken_source (selected : SelectedInventory whole row) (brokenBody : BrokenBody row.original.function.typedBody)
    (word : Core.Word) :
    Dynamic.FunctionStatementsExecute (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      selected.packet.header.context selected.packet.header.function.evidence selected.packet.header.function.source
      (wordEnvironment brokenBody.parts.binder ⟨[]⟩) (wordHeap ⟨[]⟩ word) selected.packet.header.function.body
      selected.packet.header.context (.returned (.word word)) (wordHeap ⟨[]⟩ word) := by
  rw [two_body selected brokenBody.parts.roots, selected.source_eq]
  exact brokenBody.trace selected.packet.header.function.evidence ⟨[]⟩ word

/-- The original Source execution of `counted`'s body at its header returns
its parameter after its `for` loop runs once and stops at its post header's
assignment. The header local's binder extension comes from the header's typing
certificate. -/
theorem counted_source (selected : SelectedInventory whole row)
    (countedBody : CountedBody row.original.function.typedBody)
    (certified : SelectedCompilationNamedSourceTyping.Certified selected.packet.header) (word : Core.Word) :
    Dynamic.FunctionStatementsExecute (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      selected.packet.header.context selected.packet.header.function.evidence selected.packet.header.function.source
      (wordEnvironment countedBody.parts.binder ⟨[]⟩) (wordHeap ⟨[]⟩ word) selected.packet.header.function.body
      selected.packet.header.context (.returned (.word word)) (boolHeap (wordHeap ⟨[]⟩ word) false) := by
  have body := two_body selected countedBody.parts.roots
  have unique : NodeOccurrencesUnique row.original.function.typedBody :=
    selected.source_eq ▸ selected.packet.header.unique
  obtain ⟨_final, _facts, typed, _completes⟩ := certified.statements
  rw [body, selected.source_eq] at typed
  cases typed with
  | cons head _ =>
    obtain ⟨node, contains, formTyped⟩ := Dynamic.StatementHasType.formTyping head
    cases Option.some.inj ((lookupStatement?_complete unique contains).symm.trans countedBody.parts.loopFound)
    rw [countedBody.parts.loopForm] at formTyped
    cases formTyped with
    | forLoop initial _ _ _ =>
      cases initial with
      | cons item _ =>
        cases item with
        | letInitialized _ _ _ extension =>
          rw [body, selected.source_eq]
          exact countedBody.trace selected.packet.header.function.evidence ⟨[]⟩ extension word
        | letInitializedGeneralized polymorphic =>
          exact absurd (by rw [countedBody.goScheme]; rfl) polymorphic

/-- The original Source execution of `tripled`'s body at its header returns the
triple of its parameter's word. -/
theorem tripled_source (selected : SelectedInventory whole row)
    (tripledBody : TripledBody row.original.function.typedBody) (word : Core.Word) :
    Dynamic.FunctionStatementsExecute (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      selected.packet.header.context selected.packet.header.function.evidence selected.packet.header.function.source
      (wordEnvironment tripledBody.parts.binder ⟨[]⟩) (wordHeap ⟨[]⟩ word) selected.packet.header.function.body
      selected.packet.header.context (.returned (.product (.word word) (.product (.word word) (.word word))))
      (wordHeap ⟨[]⟩ word) := by
  rw [single_body selected tripledBody.parts.roots, selected.source_eq]
  exact tripledBody.trace selected.packet.header.function.evidence ⟨[]⟩ word

/-- A typed constructor application has an admissible instantiation. -/
private theorem constructor_admissible {source : TypedSource} {context : SourceSemantics.Context}
    {id : ExpressionId} {node : ExpressionNode} {type : TypeSystem.Ty}
    {instantiation : DataConstructorInstantiation} {arguments : List ExpressionId}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .constructor instantiation arguments)
    (typing : ExpressionHasType source context id type) :
    DataConstructorInstantiation.Admissible context instantiation := by
  cases typing with
  | intro contains raw _rawEq _rawType _type _plan =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    cases same
    rw [form] at raw
    cases raw with
    | constructor valid _arguments => exact valid

/-- The original Source execution of `boxed`'s body at its header returns
`Item` applied to its parameter's word. The constructor's metadata is valid by
the header's typing certificate and its empty substitution. -/
theorem boxed_source (selected : SelectedInventory whole row)
    (boxedBody : BoxedBody row.original.function.typedBody)
    (certified : SelectedCompilationNamedSourceTyping.Certified selected.packet.header) (word : Core.Word) :
    Dynamic.FunctionStatementsExecute (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      selected.packet.header.context selected.packet.header.function.evidence selected.packet.header.function.source
      (wordEnvironment boxedBody.parts.binder ⟨[]⟩) (wordHeap ⟨[]⟩ word) selected.packet.header.function.body
      selected.packet.header.context (.returned (.constructed boxedBody.parts.instantiation [.word word]))
      (wordHeap ⟨[]⟩ word) := by
  have body := single_body selected boxedBody.parts.roots
  have unique : NodeOccurrencesUnique row.original.function.typedBody :=
    selected.source_eq ▸ selected.packet.header.unique
  obtain ⟨_final, _facts, typed, _completes⟩ := certified.statements
  rw [body, selected.source_eq] at typed
  cases typed with
  | singleton head =>
    obtain ⟨node, contains, formTyped⟩ := Dynamic.StatementHasType.formTyping head
    cases Option.some.inj ((lookupStatement?_complete unique contains).symm.trans boxedBody.parts.statementFound)
    rw [boxedBody.parts.statementForm] at formTyped
    cases formTyped with
    | returnValue expression =>
      have admissible := constructor_admissible unique boxedBody.parts.constructFound boxedBody.parts.constructForm
        expression
      have valid : DataConstructorInstantiation.Valid selected.packet.header.context boxedBody.parts.instantiation := by
        cases admissible with
        | intro dataType signature dataMember signatureMember owner constructorEq exact _range payload result =>
          exact .intro dataType signature dataMember signatureMember owner constructorEq exact
            (by rw [boxedBody.parts.substitution]; intro parameter replacement impossible; cases impossible)
            payload result
      rw [body, selected.source_eq]
      exact boxedBody.trace selected.packet.header.function.evidence ⟨[]⟩ valid word

/-- The callee premise of the fault lifting for the family that admits
`identity`'s retained instantiation: its body instance is its header's, whose
Source is `identity`'s cache row. -/
theorem identity_callees_plain (whole : WholeInventory fixture)
    (wellFormed : ProgramWellFormed (Program.ofChecked fixture.recipe.compiled.sourceProgram)) {identity : Row fixture}
    (plain : CellAwareInvocationAcceptedFaultLifting.CalleesPlain identity.original.function.typedBody) :
    CellAwareInvocationAcceptedFaultLifting.CalleesFault (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      (fun instantiation => instantiation = CallableNamedCanonicalOrder.retainedInstantiation identity.original) := by
  intro instantiation bodyInstance admits instantiates
  subst admits
  obtain ⟨selected⟩ := whole.select identity
  have frameInstantiated := selected.packet.header.frame.instantiated
  rw [selected.packet.aligned.metadata, selected.original] at frameInstantiated
  have bodySame := BuiltinNamedCalls.instantiation_unique_of_wellFormed wellFormed instantiates frameInstantiated
  subst bodySame
  rw [← selected.packet.header.frame.source, selected.source_eq]
  exact plain

/-- The first public call of a row, with the conclusions of the call root's
output theorem, its checkpoint sufficiency theorem and its checkpoint
reflection theorem. -/
structure AcceptedCall (selected : SelectedInventory whole row) (word : Word)
    (started : Started fixture row.original.key [.word word]) where
  start : SelectedCompilationPublicSessionInitial.Started whole.rows fixture.ready selected.packet.header started.call
  output : ∃ requiredExecution requiredOutput, ∀ executionFuel outputFuel
      (outcome : SourceCoreExecution.Outcome started.artifact),
    requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
    started.call.checkpoint.ResumeAt executionFuel outputFuel outcome →
    ∃ (returned : SourceCoreExecution.Completion started.artifact)
      (actual : SourceCoreIndexedSession.Completion start.artifact)
      (generation : SourceCorePublicValues.ExportGeneration) (value : Value) (finalStore : Store),
      outcome = .succeeded returned ∧
      start.checkpoint.SucceededResultAt executionFuel outputFuel generation value finalStore actual ∧
      returned.IndexedAt actual
  native : ∃ (value : Value) (finalStore : Store) (required : Nat),
    ∀ fuel, required ≤ fuel → start.checkpoint.NativeDone fuel value finalStore
  reflects : ∀ fuel (value : Value) (finalStore : Store), start.checkpoint.NativeDone fuel value finalStore →
    ∃ (sidecar : SourceCoreStageContracts.Sidecar) (size : Nat) (environment : Dynamic.Environment)
      (bound : Dynamic.Heap) (finalContext : SourceSemantics.Context) (outcome : Staging.Recursive.BodyOutcome)
      (after : Dynamic.Heap),
      Dynamic.BindersAllocate [] ⟨[]⟩ selected.packet.header.function.parameters [.word word] environment bound ∧
      Staging.Recursive.Size.Statements (Program.ofChecked fixture.recipe.compiled.sourceProgram)
        (SelectedCompilationPhysicalProgramSupport.stages fixture.recipe.compiled) size
        (RecursiveStageRegistry.scope sidecar [] selected.packet.header.function) selected.packet.header.context
        environment bound selected.packet.header.function.body finalContext outcome after ∧
      Staging.Recursive.BodyResult selected.packet.header.function.resultType outcome
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome)

/-- `accepted_call` at an original Source execution that returns any value in
any context, as one of a body that returns an integer or declares locals does. -/
theorem accepted_call_returning (selected : SelectedInventory whole row) {called : DeclarationInstantiation → Prop}
    (calls : CallRows fixture called fixture.recipe.compiled.indexed.base.functions)
    (admitted : ∀ {instantiation}, called instantiation →
      ∃ callee : Row fixture, instantiation = CallableNamedCanonicalOrder.retainedInstantiation callee.original)
    (word : Word)
    (wellFormed : ProgramWellFormed (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    (started : Started fixture row.original.key [.word word])
    (callableProfile : fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true)
    {binder : TypedBinder} (inputs : row.original.function.typedBody.inputs = [binder])
    (scheme : binder.scheme = .mono .word) {finalContext : SourceSemantics.Context} {result : Dynamic.Value}
    {after : Dynamic.Heap}
    (sourceTrace : Dynamic.FunctionStatementsExecute (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      selected.packet.header.context selected.packet.header.function.evidence selected.packet.header.function.source
      (wordEnvironment binder ⟨[]⟩) (wordHeap ⟨[]⟩ word) selected.packet.header.function.body
      finalContext (.returned result) after) :
    Nonempty (AcceptedCall selected word started) := by
  obtain ⟨types, allocated⟩ := word_parameter selected inputs scheme ⟨[]⟩ word
  have support := SelectedCompilationNamedSupport.Support.of_program wellFormed
  obtain ⟨start⟩ := CellAwarePublicInitialSelectedStart.from_selected_call
    (rows := whole.rows) (prepared := fixture.ready) (header := selected.packet.header) (call := started.call)
    fixture.accepted fixture.selected started.opened started.bootstrap started.fresh
    started.authority (.single started.ready) (fun _ member key => selected.root_selection member key)
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      selected.packet.header.function.context [.word word] selected.packet.header.types := by
    rw [types]
    exact .cons ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.word word] [.word word] :=
    .cons ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩ .nil
  obtain ⟨origin, _contextAt, _issued, _extension⟩ := CellAwarePublicInitialStart.receiver start
  obtain ⟨initial⟩ := CellAwarePublicInitialStart.of_started whole.distinct callableProfile
    origin.result.context.registry (CallableIndexedOwnedPublicDecodedCallFaults.faults origin.result.diagnostics)
    support.bodyTyping start inputTypes inputMeanings
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨selected.packet.selected.diagnostics, selected.packet.selected.found, rfl⟩
  obtain ⟨sidecar, _sidecarIssued, bodySelected⟩ := whole.invocation selected.packet selected.retained
  obtain ⟨body, covered, closed, ports⟩ := whole.call_inputs calls selected.packet
  obtain ⟨sourceCompiled, artifact, checked⟩ := CellAwarePublicAcceptedNamedRoot.compilation_receipts
    fixture.checked fixture.accepted fixture.selected
  obtain ⟨_entry, entryMember, _shape, _first⟩ := start.selected.2
  let rows : ∀ header, header ∈ headers whole.rows → called header.instantiation →
      CellAwareInvocationAcceptedCallFamily.Row (headers := headers whole.rows) called header :=
    fun _header member _ => Classical.choice (whole.family_row calls support entryMember member)
  obtain ⟨size, trace⟩ := CellAwareInvocationAcceptedCallLifting.body fixture.recipe.compiled.indexed
    (registry := SelectedCompilationPhysicalProgramSupport.stages fixture.recipe.compiled)
    ((SelectedCompilationPhysicalProgramSupport.stages fixture.recipe.compiled).source bodySelected)
    ((SelectedCompilationPhysicalProgramSupport.stages fixture.recipe.compiled).evidence bodySelected)
    selected.packet.header.unique (whole.callees calls wellFormed admitted)
    (fun _ => CellAwareInvocationAcceptedCallLifting.ClosuresFramed.stages fixture.recipe.compiled bodySelected)
    (fun _ => CellAwareInvocationAcceptedCallLifting.ClosuresFramed.stages fixture.recipe.compiled)
    (fun _ => CellAwareInvocationAcceptedCallLifting.Aligned.of_wellFormed wellFormed)
    (calls.header_shape selected.packet)
    (fun _ => CellAwareInvocationAcceptedStoredFunctions.Heap.empty.push fun _ same => by cases same; exact .word word)
    sourceTrace
  obtain ⟨_capture, _value, _finalStore, _finalMap, _finalWorld, requiredExecution, requiredOutput, _result, output⟩ :=
    CellAwarePublicAcceptedCallForward.first_value_selected callableProfile initial.issued prepared
      selected.packet.aligned fixture.ready diagnostic support start.selected (owner fixture.recipe.compiled)
      initial.caller.base.val initial.globalReference initial.keyPhysical initial.caller.physical initial.stable
      initial.heapTyped initial.argumentsTyped bodySelected artifact checked body covered initial.represented
      initial.heaps rfl start.started start.atCheckpoint
      (congrArg SourceCoreCompatibleValues.Context.registry initial.contextAt) initial.exportsReady allocated trace
      (CellAwarePublicAcceptedCallRoot.expressions_of_family callableProfile initial.issued prepared
        selected.packet.aligned diagnostic support artifact checked closed ports
        (fun _ => CellAwareNamedValuePorts.ports whole.rows whole.complete prepared.compilation) wellFormed rows size)
  obtain ⟨_capture, value, finalStore, _finalMap, _finalWorld, required, run, _result⟩ :=
    CellAwarePublicAcceptedCallRoot.checkpoint_has_sufficient_fuel_selected callableProfile initial.issued prepared
      selected.packet.aligned fixture.ready diagnostic support start.selected (owner fixture.recipe.compiled)
      initial.caller.base.val initial.globalReference initial.keyPhysical initial.caller.physical initial.stable
      initial.heapTyped initial.argumentsTyped bodySelected artifact checked body covered initial.represented
      initial.heaps rfl start.started allocated trace
      (CellAwarePublicAcceptedCallRoot.expressions_of_family callableProfile initial.issued prepared
        selected.packet.aligned diagnostic support artifact checked closed ports
        (fun _ => CellAwareNamedValuePorts.ports whole.rows whole.complete prepared.compilation) wellFormed rows size)
  refine ⟨⟨start, ⟨requiredExecution, requiredOutput, ?_⟩, ⟨value, finalStore, required, run⟩, ?_⟩⟩
  · intro executionFuel outputFuel outcome enoughExecution enoughOutput resumed
    obtain ⟨returned, actual, generation, _reached, same, succeeded, indexed, _⟩ :=
      output executionFuel outputFuel outcome enoughExecution enoughOutput resumed
    exact ⟨returned, actual, generation, _, _, same, succeeded, indexed⟩
  · intro fuel completedValue completedStore completed
    obtain ⟨_capture, size, environment, bound, finalContext, outcome, after, _finalMap, _finalWorld,
        allocated, staged, result, _named⟩ :=
      CellAwarePublicAcceptedCallRoot.checkpoint_reflects_selected callableProfile initial.issued prepared
        selected.packet.aligned fixture.ready diagnostic support start.selected (owner fixture.recipe.compiled)
        initial.caller.base.val initial.globalReference initial.keyPhysical initial.caller.physical initial.stable
        initial.heapTyped initial.argumentsTyped bodySelected artifact checked body covered initial.represented
        initial.heaps rfl start.started completed
        (CellAwarePublicAcceptedCallRoot.expressions_of_family callableProfile initial.issued prepared
          selected.packet.aligned diagnostic support artifact checked closed ports
          (fun _ => CellAwareNamedValuePorts.ports whole.rows whole.complete prepared.compilation) wellFormed rows)
    exact ⟨sidecar, size, environment, bound, finalContext, outcome, after, allocated, staged, result⟩

/-- `accepted_call` at an original Source execution that ends in any context,
as one of a body with local declarations does. -/
theorem accepted_call_with_locals (selected : SelectedInventory whole row) {called : DeclarationInstantiation → Prop}
    (calls : CallRows fixture called fixture.recipe.compiled.indexed.base.functions)
    (admitted : ∀ {instantiation}, called instantiation →
      ∃ callee : Row fixture, instantiation = CallableNamedCanonicalOrder.retainedInstantiation callee.original)
    (word : Word)
    (wellFormed : ProgramWellFormed (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    (started : Started fixture row.original.key [.word word])
    (callableProfile : fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true)
    {binder : TypedBinder} (inputs : row.original.function.typedBody.inputs = [binder])
    (scheme : binder.scheme = .mono .word) {finalContext : SourceSemantics.Context} {result : Word}
    {after : Dynamic.Heap}
    (sourceTrace : Dynamic.FunctionStatementsExecute (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      selected.packet.header.context selected.packet.header.function.evidence selected.packet.header.function.source
      (wordEnvironment binder ⟨[]⟩) (wordHeap ⟨[]⟩ word) selected.packet.header.function.body
      finalContext (.returned (.word result)) after) :
    Nonempty (AcceptedCall selected word started) :=
  accepted_call_returning selected calls admitted word wellFormed started callableProfile inputs scheme sourceTrace

/-- Every premise is an original checked or static observation, a runtime check
of the program's rows, an actual public start, or the row's original Source
execution after the allocation of its `Word` parameter. The body's
accepted-expression meaning comes from the family of the checked rows, and the
staged Source trace is lifted from the original execution through the checked
shape, with the admitted callees' static receipts from the inventory. -/
theorem accepted_call (selected : SelectedInventory whole row) {called : DeclarationInstantiation → Prop}
    (calls : CallRows fixture called fixture.recipe.compiled.indexed.base.functions)
    (admitted : ∀ {instantiation}, called instantiation →
      ∃ callee : Row fixture, instantiation = CallableNamedCanonicalOrder.retainedInstantiation callee.original)
    (word : Word)
    (wellFormed : ProgramWellFormed (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    (started : Started fixture row.original.key [.word word])
    (callableProfile : fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true)
    {binder : TypedBinder} (inputs : row.original.function.typedBody.inputs = [binder])
    (scheme : binder.scheme = .mono .word) {result : Word} {after : Dynamic.Heap}
    (sourceTrace : Dynamic.FunctionStatementsExecute (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      selected.packet.header.context selected.packet.header.function.evidence selected.packet.header.function.source
      (wordEnvironment binder ⟨[]⟩) (wordHeap ⟨[]⟩ word) selected.packet.header.function.body
      selected.packet.header.context (.returned (.word result)) after) :
    Nonempty (AcceptedCall selected word started) :=
  accepted_call_with_locals selected calls admitted word wellFormed started callableProfile inputs scheme sourceTrace

/-- The first public call of a row with the conclusion of the call root's
checkpoint reflection theorem alone. -/
structure AcceptedReflection (selected : SelectedInventory whole row) (word : Word)
    (started : Started fixture row.original.key [.word word]) where
  start : SelectedCompilationPublicSessionInitial.Started whole.rows fixture.ready selected.packet.header started.call
  reflects : ∀ fuel (value : Value) (finalStore : Store), start.checkpoint.NativeDone fuel value finalStore →
    ∃ (sidecar : SourceCoreStageContracts.Sidecar) (size : Nat) (environment : Dynamic.Environment)
      (bound : Dynamic.Heap) (finalContext : SourceSemantics.Context) (outcome : Staging.Recursive.BodyOutcome)
      (after : Dynamic.Heap),
      Dynamic.BindersAllocate [] ⟨[]⟩ selected.packet.header.function.parameters [.word word] environment bound ∧
      Staging.Recursive.Size.Statements (Program.ofChecked fixture.recipe.compiled.sourceProgram)
        (SelectedCompilationPhysicalProgramSupport.stages fixture.recipe.compiled) size
        (RecursiveStageRegistry.scope sidecar [] selected.packet.header.function) selected.packet.header.context
        environment bound selected.packet.header.function.body finalContext outcome after ∧
      Staging.Recursive.BodyResult selected.packet.header.function.resultType outcome
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome)

/-- The reflection part of `accepted_call`, which needs no Source execution, so
it applies at every argument word. -/
theorem accepted_reflection (selected : SelectedInventory whole row) {called : DeclarationInstantiation → Prop}
    (calls : CallRows fixture called fixture.recipe.compiled.indexed.base.functions) (word : Word)
    (wellFormed : ProgramWellFormed (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    (started : Started fixture row.original.key [.word word])
    (callableProfile : fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true)
    {binder : TypedBinder} (inputs : row.original.function.typedBody.inputs = [binder])
    (scheme : binder.scheme = .mono .word) :
    Nonempty (AcceptedReflection selected word started) := by
  obtain ⟨types, _allocated⟩ := word_parameter selected inputs scheme ⟨[]⟩ word
  have support := SelectedCompilationNamedSupport.Support.of_program wellFormed
  obtain ⟨start⟩ := CellAwarePublicInitialSelectedStart.from_selected_call
    (rows := whole.rows) (prepared := fixture.ready) (header := selected.packet.header) (call := started.call)
    fixture.accepted fixture.selected started.opened started.bootstrap started.fresh
    started.authority (.single started.ready) (fun _ member key => selected.root_selection member key)
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      selected.packet.header.function.context [.word word] selected.packet.header.types := by
    rw [types]
    exact .cons ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.word word] [.word word] :=
    .cons ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩ .nil
  obtain ⟨origin, _contextAt, _issued, _extension⟩ := CellAwarePublicInitialStart.receiver start
  obtain ⟨initial⟩ := CellAwarePublicInitialStart.of_started whole.distinct callableProfile
    origin.result.context.registry (CallableIndexedOwnedPublicDecodedCallFaults.faults origin.result.diagnostics)
    support.bodyTyping start inputTypes inputMeanings
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨selected.packet.selected.diagnostics, selected.packet.selected.found, rfl⟩
  obtain ⟨sidecar, _sidecarIssued, bodySelected⟩ := whole.invocation selected.packet selected.retained
  obtain ⟨body, covered, closed, ports⟩ := whole.call_inputs calls selected.packet
  obtain ⟨_sourceCompiled, artifact, checked⟩ := CellAwarePublicAcceptedNamedRoot.compilation_receipts
    fixture.checked fixture.accepted fixture.selected
  obtain ⟨_entry, entryMember, _shape, _first⟩ := start.selected.2
  let rows : ∀ header, header ∈ headers whole.rows → called header.instantiation →
      CellAwareInvocationAcceptedCallFamily.Row (headers := headers whole.rows) called header :=
    fun _header member _ => Classical.choice (whole.family_row calls support entryMember member)
  refine ⟨⟨start, ?_⟩⟩
  intro fuel completedValue completedStore completed
  obtain ⟨_capture, size, environment, bound, finalContext, outcome, after, _finalMap, _finalWorld,
      allocated, staged, result, _named⟩ :=
    CellAwarePublicAcceptedCallRoot.checkpoint_reflects_selected callableProfile initial.issued prepared
      selected.packet.aligned fixture.ready diagnostic support start.selected (owner fixture.recipe.compiled)
      initial.caller.base.val initial.globalReference initial.keyPhysical initial.caller.physical initial.stable
      initial.heapTyped initial.argumentsTyped bodySelected artifact checked body covered initial.represented
      initial.heaps rfl start.started completed
      (CellAwarePublicAcceptedCallRoot.expressions_of_family callableProfile initial.issued prepared
        selected.packet.aligned diagnostic support artifact checked closed ports
        (fun _ => CellAwareNamedValuePorts.ports whole.rows whole.complete prepared.compilation) wellFormed rows)
  exact ⟨sidecar, size, environment, bound, finalContext, outcome, after, allocated, staged, result⟩

/-- The first public call of a row whose original Source execution faults,
with the conclusion of the call root's failure theorem: the actual resumption
fails with a token that represents the fault at the call's public diagnostic
table. -/
structure AcceptedFailure (selected : SelectedInventory whole row) (word : Word)
    (started : Started fixture row.original.key [.word word]) (reason : Dynamic.SemanticFault) where
  start : SelectedCompilationPublicSessionInitial.Started whole.rows fixture.ready selected.packet.header started.call
  output : ∃ (table : SourceCoreFaultSites.Table) (token : Word) (requiredExecution : Nat),
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults table (.semantic reason) token ∧
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome started.artifact),
      requiredExecution ≤ executionFuel → started.call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ (returned : SourceCoreExecution.Session started.artifact)
        (actual : SourceCoreIndexedSession.Session start.artifact) (value : Value) (finalStore : Store),
        outcome = .failed token returned ∧ start.checkpoint.FailedResultAt executionFuel value finalStore token actual ∧
        returned.IndexedAt actual

/-- As `accepted_call`, from the row's original Source execution that faults
with an expressible reason: the staged fault trace is lifted from it through
the checked shape, given that the direct calls of the row and of the admitted
callees have plain callees, and the call root's failure theorem applies at the
first public call. -/
theorem accepted_failure (selected : SelectedInventory whole row) {called : DeclarationInstantiation → Prop}
    (calls : CallRows fixture called fixture.recipe.compiled.indexed.base.functions)
    (admitted : ∀ {instantiation}, called instantiation →
      ∃ callee : Row fixture, instantiation = CallableNamedCanonicalOrder.retainedInstantiation callee.original)
    (word : Word)
    (wellFormed : ProgramWellFormed (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    (started : Started fixture row.original.key [.word word])
    (callableProfile : fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true)
    {binder : TypedBinder} (inputs : row.original.function.typedBody.inputs = [binder])
    (scheme : binder.scheme = .mono .word)
    (plain : CellAwareInvocationAcceptedFaultLifting.CalleesPlain row.original.function.typedBody)
    (calleesPlain : CellAwareInvocationAcceptedFaultLifting.CalleesFault
      (Program.ofChecked fixture.recipe.compiled.sourceProgram) called)
    {reason : Dynamic.SemanticFault} (expressible : CellAwareInvocationAcceptedFaultLifting.Expressible reason)
    {finalContext : SourceSemantics.Context} {after : Dynamic.Heap}
    (sourceFault : Dynamic.FunctionStatementsFault (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      selected.packet.header.context selected.packet.header.function.evidence selected.packet.header.function.source
      (wordEnvironment binder ⟨[]⟩) (wordHeap ⟨[]⟩ word) selected.packet.header.function.body
      finalContext reason after) :
    Nonempty (AcceptedFailure selected word started reason) := by
  obtain ⟨types, allocated⟩ := word_parameter selected inputs scheme ⟨[]⟩ word
  have support := SelectedCompilationNamedSupport.Support.of_program wellFormed
  obtain ⟨start⟩ := CellAwarePublicInitialSelectedStart.from_selected_call
    (rows := whole.rows) (prepared := fixture.ready) (header := selected.packet.header) (call := started.call)
    fixture.accepted fixture.selected started.opened started.bootstrap started.fresh
    started.authority (.single started.ready) (fun _ member key => selected.root_selection member key)
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      selected.packet.header.function.context [.word word] selected.packet.header.types := by
    rw [types]
    exact .cons ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.word word] [.word word] :=
    .cons ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩ .nil
  obtain ⟨origin, _contextAt, _issued, _extension⟩ := CellAwarePublicInitialStart.receiver start
  obtain ⟨initial⟩ := CellAwarePublicInitialStart.of_started whole.distinct callableProfile
    origin.result.context.registry (CallableIndexedOwnedPublicDecodedCallFaults.faults origin.result.diagnostics)
    support.bodyTyping start inputTypes inputMeanings
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨selected.packet.selected.diagnostics, selected.packet.selected.found, rfl⟩
  obtain ⟨sidecar, _sidecarIssued, bodySelected⟩ := whole.invocation selected.packet selected.retained
  obtain ⟨body, covered, closed, ports⟩ := whole.call_inputs calls selected.packet
  obtain ⟨sourceCompiled, artifact, checked⟩ := CellAwarePublicAcceptedNamedRoot.compilation_receipts
    fixture.checked fixture.accepted fixture.selected
  obtain ⟨_entry, entryMember, _shape, _first⟩ := start.selected.2
  let rows : ∀ header, header ∈ headers whole.rows → called header.instantiation →
      CellAwareInvocationAcceptedCallFamily.Row (headers := headers whole.rows) called header :=
    fun _header member _ => Classical.choice (whole.family_row calls support entryMember member)
  obtain ⟨size, trace⟩ := CellAwareInvocationAcceptedFaultLifting.body_fault fixture.recipe.compiled.indexed
    (registry := SelectedCompilationPhysicalProgramSupport.stages fixture.recipe.compiled)
    ((SelectedCompilationPhysicalProgramSupport.stages fixture.recipe.compiled).source bodySelected)
    ((SelectedCompilationPhysicalProgramSupport.stages fixture.recipe.compiled).evidence bodySelected)
    selected.packet.header.unique (selected.source_eq ▸ plain) (whole.callees calls wellFormed admitted)
    calleesPlain (calls.header_shape selected.packet) (header_signatures selected.packet.header) expressible
    (fun _ => CellAwareInvocationAcceptedStoredFunctions.Heap.empty.push fun _ same => by cases same; exact .word word)
    sourceFault
  obtain ⟨_capture, _value, _finalStore, _finalMap, _finalWorld, requiredExecution, token, _result, represented,
      output⟩ :=
    CellAwarePublicAcceptedCallForward.first_fault_selected callableProfile initial.issued prepared
      selected.packet.aligned fixture.ready diagnostic support start.selected (owner fixture.recipe.compiled)
      initial.caller.base.val initial.globalReference initial.keyPhysical initial.caller.physical initial.stable
      initial.heapTyped initial.argumentsTyped bodySelected artifact checked body covered initial.represented
      initial.heaps rfl start.started start.atCheckpoint
      (congrArg SourceCoreCompatibleValues.Context.registry initial.contextAt) initial.exportsReady allocated trace
      (CellAwarePublicAcceptedCallRoot.expressions_of_family callableProfile initial.issued prepared
        selected.packet.aligned diagnostic support artifact checked closed ports
        (fun _ => CellAwareNamedValuePorts.ports whole.rows whole.complete prepared.compilation) wellFormed rows size)
  refine ⟨⟨start, _, token, requiredExecution, represented, ?_⟩⟩
  intro executionFuel outputFuel outcome enough resumed
  obtain ⟨returned, actual, _reached, same, failed, indexed, _⟩ :=
    output executionFuel outputFuel outcome enough resumed
  exact ⟨returned, actual, _, _, same, failed, indexed⟩

/-- The receipts that the runtime checks observe: the compiled program, its
cache, `identity`'s row and body, the checked rows of the family that admits
`identity`'s retained instantiation, the program typing, the callable profile
and the plain callees of `identity`'s body. -/
structure Observed where
  fixture : CompiledFixture workspace options
  cache : ObservedCache fixture fixture.recipe.compiled.indexed.base.functions
  identity : Row fixture
  identityBody : IdentityBody identity.original.function.typedBody
  calls : CallRows fixture (fun instantiation => instantiation =
    CallableNamedCanonicalOrder.retainedInstantiation identity.original) fixture.recipe.compiled.indexed.base.functions
  wellFormed : ProgramWellFormed (Program.ofChecked fixture.recipe.compiled.sourceProgram)
  callableProfile : fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true
  identityPlain : CellAwareInvocationAcceptedFaultLifting.CalleesPlain identity.original.function.typedBody

def observe : IO Observed := do
  let fixture ← compileFixture workspace options
  let cache ← observeCache fixture fixture.recipe.compiled.indexed.base.functions
  let identity ← observeRow fixture "identity"
  let identityBody ← observeIdentityBody identity.original.function.typedBody
  let calls ← observeCallRows fixture
    (fun instantiation => instantiation = CallableNamedCanonicalOrder.retainedInstantiation identity.original)
    fixture.recipe.compiled.indexed.base.functions
  let ⟨wellFormed⟩ ← observeWellFormed fixture.checked
  let ⟨callableProfile⟩ ← observed (fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true)
    "calls actual callable profile"
  let ⟨identityPlain⟩ ← observed
    (CellAwareInvocationAcceptedFaultLifting.CalleesPlain identity.original.function.typedBody) "identity callees"
  return ⟨fixture, cache, identity, identityBody, calls, wellFormed, callableProfile, identityPlain⟩

namespace AcceptedCallRuntime

/-- Each call starts a fresh actual session. The plan is kernel-checked against
whatever the observed compile, check, row and start receipts are; the resume
runs the real compiled code. -/
def run : IO Unit := do
  let observed ← observe
  let relay ← observeRow observed.fixture "relay"
  let relayBody ← observeRelayBody observed.fixture
    (CallableNamedCanonicalOrder.retainedInstantiation observed.identity.original) relay.original.function.typedBody
  for word in [Word.zero, Word.ofNatModulo 7] do
    let started ← observeStarted observed.fixture relay.original.key [.word word]
    have _plan : ∃ (whole : WholeInventory observed.fixture) (selected : SelectedInventory whole relay),
        Nonempty (AcceptedCall selected word started) := by
      obtain ⟨whole⟩ := observed.fixture.inventory observed.cache observed.wellFormed
      obtain ⟨selected⟩ := whole.select relay
      obtain ⟨identitySelected⟩ := whole.select observed.identity
      exact ⟨whole, selected, accepted_call selected observed.calls (fun admits => ⟨observed.identity, admits⟩)
        word observed.wellFormed started observed.callableProfile relayBody.inputs relayBody.binderScheme
        (relay_source selected identitySelected observed.calls observed.identityBody relayBody word)⟩
    let result ← started.call.checkpoint.resumeWithReceipt runOptions.executionFuel runOptions.outputValidationFuel
    match result.val with
    | .succeeded returned =>
      unless returned.value == .word word do throw (IO.userError "accepted call output changed")
    | _ => throw (IO.userError "accepted call did not succeed")
  IO.println "ACCEPTED_CALL_PUBLIC_PASS"

end AcceptedCallRuntime

namespace AcceptedNestedCallRuntime

/-- As `AcceptedCallRuntime.run`, at `twice`, whose call has a call as its
argument. -/
def run : IO Unit := do
  let observed ← observe
  let twice ← observeRow observed.fixture "twice"
  let twiceBody ← observeTwiceBody observed.fixture
    (CallableNamedCanonicalOrder.retainedInstantiation observed.identity.original) twice.original.function.typedBody
  for word in [Word.zero, Word.ofNatModulo 7] do
    let started ← observeStarted observed.fixture twice.original.key [.word word]
    have _plan : ∃ (whole : WholeInventory observed.fixture) (selected : SelectedInventory whole twice),
        Nonempty (AcceptedCall selected word started) := by
      obtain ⟨whole⟩ := observed.fixture.inventory observed.cache observed.wellFormed
      obtain ⟨selected⟩ := whole.select twice
      obtain ⟨identitySelected⟩ := whole.select observed.identity
      exact ⟨whole, selected, accepted_call selected observed.calls (fun admits => ⟨observed.identity, admits⟩)
        word observed.wellFormed started observed.callableProfile twiceBody.parts.inputs twiceBody.binderScheme
        (twice_source selected identitySelected observed.calls observed.identityBody twiceBody word)⟩
    let result ← started.call.checkpoint.resumeWithReceipt runOptions.executionFuel runOptions.outputValidationFuel
    match result.val with
    | .succeeded returned =>
      unless returned.value == .word word do throw (IO.userError "accepted nested call output changed")
    | _ => throw (IO.userError "accepted nested call did not succeed")
  IO.println "ACCEPTED_NESTED_CALL_PUBLIC_PASS"

end AcceptedNestedCallRuntime

namespace AcceptedTailRuntime

/-- As `AcceptedCallRuntime.run`, at `tailed`, whose body ends in the direct
call of `identity` as its final value. -/
def run : IO Unit := do
  let observed ← observe
  let tailed ← observeRow observed.fixture "tailed"
  let tailedBody ← observeTailedBody observed.fixture
    (CallableNamedCanonicalOrder.retainedInstantiation observed.identity.original) tailed.original.function.typedBody
  for word in [Word.zero, Word.ofNatModulo 7] do
    let started ← observeStarted observed.fixture tailed.original.key [.word word]
    have _plan : ∃ (whole : WholeInventory observed.fixture) (selected : SelectedInventory whole tailed),
        Nonempty (AcceptedCall selected word started) := by
      obtain ⟨whole⟩ := observed.fixture.inventory observed.cache observed.wellFormed
      obtain ⟨selected⟩ := whole.select tailed
      obtain ⟨identitySelected⟩ := whole.select observed.identity
      exact ⟨whole, selected, accepted_call selected observed.calls (fun admits => ⟨observed.identity, admits⟩)
        word observed.wellFormed started observed.callableProfile tailedBody.inputs tailedBody.binderScheme
        (tailed_source selected identitySelected observed.calls observed.identityBody tailedBody word)⟩
    let result ← started.call.checkpoint.resumeWithReceipt runOptions.executionFuel runOptions.outputValidationFuel
    match result.val with
    | .succeeded returned =>
      unless returned.value == .word word do throw (IO.userError "accepted tail value output changed")
    | _ => throw (IO.userError "accepted tail value did not succeed")
  IO.println "ACCEPTED_TAIL_PUBLIC_PASS"

end AcceptedTailRuntime

namespace AcceptedMappingRuntime

/-- As `AcceptedCallRuntime.run`, at `stored`, whose index read of its local
mapping finds the word that its assignment through the same index wrote, at
words other than the default. -/
def run : IO Unit := do
  let observed ← observe
  let stored ← observeRow observed.fixture "stored"
  let storedBody ← observeStoredBody stored.original.function.typedBody
  for word in [Word.ofNatModulo 7, Word.maximum] do
    let started ← observeStarted observed.fixture stored.original.key [.word word]
    have _plan : ∃ (whole : WholeInventory observed.fixture) (selected : SelectedInventory whole stored),
        Nonempty (AcceptedCall selected word started) := by
      obtain ⟨whole⟩ := observed.fixture.inventory observed.cache observed.wellFormed
      obtain ⟨selected⟩ := whole.select stored
      obtain ⟨_, sourceTrace⟩ := stored_source selected storedBody
        ((SelectedCompilationNamedSupport.Support.of_program observed.wellFormed).certified selected.packet.header)
        word
      exact ⟨whole, selected, accepted_call_with_locals selected observed.calls
        (fun admits => ⟨observed.identity, admits⟩) word observed.wellFormed started observed.callableProfile
        storedBody.parts.inputs storedBody.binderScheme sourceTrace⟩
    let result ← started.call.checkpoint.resumeWithReceipt runOptions.executionFuel runOptions.outputValidationFuel
    match result.val with
    | .succeeded returned =>
      unless returned.value == .word word do throw (IO.userError "accepted mapping output changed")
    | _ => throw (IO.userError "accepted mapping did not succeed")
  IO.println "ACCEPTED_MAPPING_PUBLIC_PASS"

end AcceptedMappingRuntime

namespace AcceptedBuiltinRuntime

/-- As `AcceptedCallRuntime.run`, at `summed`, which returns the integer sum of
its parameter's word with itself through calls of the builtin closures
`integerAdd` and `wordToInteger`; the sum at `Word.maximum` is beyond any
word. -/
def run : IO Unit := do
  let observed ← observe
  let summed ← observeRow observed.fixture "summed"
  let summedBody ← observeSummedBody summed.original.function.typedBody
  for word in [Word.ofNatModulo 7, Word.maximum] do
    let started ← observeStarted observed.fixture summed.original.key [.word word]
    have _plan : ∃ (whole : WholeInventory observed.fixture) (selected : SelectedInventory whole summed),
        Nonempty (AcceptedCall selected word started) := by
      obtain ⟨whole⟩ := observed.fixture.inventory observed.cache observed.wellFormed
      obtain ⟨selected⟩ := whole.select summed
      exact ⟨whole, selected, accepted_call_returning selected observed.calls
        (fun admits => ⟨observed.identity, admits⟩) word observed.wellFormed started observed.callableProfile
        summedBody.parts.inputs summedBody.binderScheme (summed_source selected summedBody word)⟩
    let result ← started.call.checkpoint.resumeWithReceipt runOptions.executionFuel runOptions.outputValidationFuel
    match result.val with
    | .succeeded returned =>
      unless returned.value == .integer (Int.ofNat word.val + Int.ofNat word.val) do
        throw (IO.userError "accepted builtin output changed")
    | _ => throw (IO.userError "accepted builtin did not succeed")
  IO.println "ACCEPTED_BUILTIN_PUBLIC_PASS"

end AcceptedBuiltinRuntime

namespace AcceptedOpcodeRuntime

/-- As `AcceptedCallRuntime.run`, at `zeroed`, which returns the opcode
`iszero` on its parameter, imported from `std.opcodes`: 1 at 0 and 0 at 7. -/
def run : IO Unit := do
  let observed ← observe
  let zeroed ← observeRow observed.fixture "zeroed"
  let zeroedBody ← observeZeroedBody zeroed.original.function.typedBody
  for word in [Word.zero, Word.ofNatModulo 7] do
    let started ← observeStarted observed.fixture zeroed.original.key [.word word]
    have _plan : ∃ (whole : WholeInventory observed.fixture) (selected : SelectedInventory whole zeroed),
        Nonempty (AcceptedCall selected word started) := by
      obtain ⟨whole⟩ := observed.fixture.inventory observed.cache observed.wellFormed
      obtain ⟨selected⟩ := whole.select zeroed
      exact ⟨whole, selected, accepted_call selected observed.calls (fun admits => ⟨observed.identity, admits⟩)
        word observed.wellFormed started observed.callableProfile zeroedBody.parts.inputs zeroedBody.binderScheme
        (zeroed_source selected zeroedBody word)⟩
    let result ← started.call.checkpoint.resumeWithReceipt runOptions.executionFuel runOptions.outputValidationFuel
    match result.val with
    | .succeeded returned =>
      unless returned.value == .word (if word == Word.zero then Word.ofNatModulo 1 else Word.zero) do
        throw (IO.userError "accepted opcode output changed")
    | _ => throw (IO.userError "accepted opcode did not succeed")
  IO.println "ACCEPTED_OPCODE_PUBLIC_PASS"

end AcceptedOpcodeRuntime

namespace AcceptedProjectedBitNotRuntime

/-- As `AcceptedCallRuntime.run`, at `inverted`, whose index read of its local
mapping finds the complement of the default word that its in-place `~` through
the same index put there. -/
def run : IO Unit := do
  let observed ← observe
  let inverted ← observeRow observed.fixture "inverted"
  let invertedBody ← observeInvertedBody inverted.original.function.typedBody
  for word in [Word.zero, Word.ofNatModulo 7] do
    let started ← observeStarted observed.fixture inverted.original.key [.word word]
    have _plan : ∃ (whole : WholeInventory observed.fixture) (selected : SelectedInventory whole inverted),
        Nonempty (AcceptedCall selected word started) := by
      obtain ⟨whole⟩ := observed.fixture.inventory observed.cache observed.wellFormed
      obtain ⟨selected⟩ := whole.select inverted
      obtain ⟨_, sourceTrace⟩ := inverted_source selected invertedBody
        ((SelectedCompilationNamedSupport.Support.of_program observed.wellFormed).certified selected.packet.header)
        word
      exact ⟨whole, selected, accepted_call_with_locals selected observed.calls
        (fun admits => ⟨observed.identity, admits⟩) word observed.wellFormed started observed.callableProfile
        invertedBody.parts.inputs invertedBody.binderScheme sourceTrace⟩
    let result ← started.call.checkpoint.resumeWithReceipt runOptions.executionFuel runOptions.outputValidationFuel
    match result.val with
    | .succeeded returned =>
      unless returned.value == .word Core.Word.zero.bitNot do
        throw (IO.userError "accepted projected bit-not output changed")
    | _ => throw (IO.userError "accepted projected bit-not did not succeed")
  IO.println "ACCEPTED_PROJECTED_BIT_NOT_PUBLIC_PASS"

end AcceptedProjectedBitNotRuntime

namespace AcceptedLoopRuntime

/-- As `AcceptedCallRuntime.run`, at `broken`, whose `while (true)` loop
breaks at once before the return of its parameter, and at `counted`, whose
`for` loop continues once and stops at its post header's assignment. -/
def run : IO Unit := do
  let observed ← observe
  let broken ← observeRow observed.fixture "broken"
  let brokenBody ← observeBrokenBody broken.original.function.typedBody
  for word in [Word.zero, Word.ofNatModulo 7] do
    let started ← observeStarted observed.fixture broken.original.key [.word word]
    have _plan : ∃ (whole : WholeInventory observed.fixture) (selected : SelectedInventory whole broken),
        Nonempty (AcceptedCall selected word started) := by
      obtain ⟨whole⟩ := observed.fixture.inventory observed.cache observed.wellFormed
      obtain ⟨selected⟩ := whole.select broken
      exact ⟨whole, selected, accepted_call selected observed.calls (fun admits => ⟨observed.identity, admits⟩)
        word observed.wellFormed started observed.callableProfile brokenBody.parts.inputs brokenBody.binderScheme
        (broken_source selected brokenBody word)⟩
    let result ← started.call.checkpoint.resumeWithReceipt runOptions.executionFuel runOptions.outputValidationFuel
    match result.val with
    | .succeeded returned =>
      unless returned.value == .word word do
        throw (IO.userError "accepted loop output changed")
    | _ => throw (IO.userError "accepted loop did not succeed")
  let counted ← observeRow observed.fixture "counted"
  let countedBody ← observeCountedBody counted.original.function.typedBody
  for word in [Word.zero, Word.ofNatModulo 7] do
    let started ← observeStarted observed.fixture counted.original.key [.word word]
    have _plan : ∃ (whole : WholeInventory observed.fixture) (selected : SelectedInventory whole counted),
        Nonempty (AcceptedCall selected word started) := by
      obtain ⟨whole⟩ := observed.fixture.inventory observed.cache observed.wellFormed
      obtain ⟨selected⟩ := whole.select counted
      exact ⟨whole, selected, accepted_call selected observed.calls (fun admits => ⟨observed.identity, admits⟩)
        word observed.wellFormed started observed.callableProfile countedBody.parts.inputs countedBody.binderScheme
        (counted_source selected countedBody
          ((SelectedCompilationNamedSupport.Support.of_program observed.wellFormed).certified selected.packet.header)
          word)⟩
    let result ← started.call.checkpoint.resumeWithReceipt runOptions.executionFuel runOptions.outputValidationFuel
    match result.val with
    | .succeeded returned =>
      unless returned.value == .word word do
        throw (IO.userError "accepted for loop output changed")
    | _ => throw (IO.userError "accepted for loop did not succeed")
  IO.println "ACCEPTED_LOOP_PUBLIC_PASS"

end AcceptedLoopRuntime

namespace AcceptedTupleRuntime

/-- As `AcceptedCallRuntime.run`, at `tripled`, which returns the triple of its
parameter's word, a tuple beyond pairs (`accepted_call_returning`). -/
def run : IO Unit := do
  let observed ← observe
  let tripled ← observeRow observed.fixture "tripled"
  let tripledBody ← observeTripledBody tripled.original.function.typedBody
  for word in [Word.zero, Word.ofNatModulo 7] do
    let started ← observeStarted observed.fixture tripled.original.key [.word word]
    have _plan : ∃ (whole : WholeInventory observed.fixture) (selected : SelectedInventory whole tripled),
        Nonempty (AcceptedCall selected word started) := by
      obtain ⟨whole⟩ := observed.fixture.inventory observed.cache observed.wellFormed
      obtain ⟨selected⟩ := whole.select tripled
      exact ⟨whole, selected, accepted_call_returning selected observed.calls
        (fun admits => ⟨observed.identity, admits⟩) word observed.wellFormed started observed.callableProfile
        tripledBody.parts.inputs tripledBody.binderScheme (tripled_source selected tripledBody word)⟩
    let result ← started.call.checkpoint.resumeWithReceipt runOptions.executionFuel runOptions.outputValidationFuel
    match result.val with
    | .succeeded returned =>
      unless returned.value == .product (.word word) (.product (.word word) (.word word)) do
        throw (IO.userError "accepted tuple output changed")
    | _ => throw (IO.userError "accepted tuple did not succeed")
  IO.println "ACCEPTED_TUPLE_PUBLIC_PASS"

end AcceptedTupleRuntime

namespace AcceptedConstructorRuntime

/-- As `AcceptedCallRuntime.run`, at `boxed`, which returns `Item` applied to
its parameter's word, a constructor application (`accepted_call_returning`). -/
def run : IO Unit := do
  let observed ← observe
  let boxed ← observeRow observed.fixture "boxed"
  let boxedBody ← observeBoxedBody boxed.original.function.typedBody
  for word in [Word.zero, Word.ofNatModulo 7] do
    let started ← observeStarted observed.fixture boxed.original.key [.word word]
    have _plan : ∃ (whole : WholeInventory observed.fixture) (selected : SelectedInventory whole boxed),
        Nonempty (AcceptedCall selected word started) := by
      obtain ⟨whole⟩ := observed.fixture.inventory observed.cache observed.wellFormed
      obtain ⟨selected⟩ := whole.select boxed
      exact ⟨whole, selected, accepted_call_returning selected observed.calls
        (fun admits => ⟨observed.identity, admits⟩) word observed.wellFormed started observed.callableProfile
        boxedBody.parts.inputs boxedBody.binderScheme
        (boxed_source selected boxedBody
          ((SelectedCompilationNamedSupport.Support.of_program observed.wellFormed).certified selected.packet.header)
          word)⟩
    let result ← started.call.checkpoint.resumeWithReceipt runOptions.executionFuel runOptions.outputValidationFuel
    match result.val with
    | .succeeded returned =>
      unless returned.value == .constructed boxedBody.parts.instantiation [.word word] do
        throw (IO.userError "accepted constructor output changed")
    | _ => throw (IO.userError "accepted constructor did not succeed")
  IO.println "ACCEPTED_CONSTRUCTOR_PUBLIC_PASS"

end AcceptedConstructorRuntime

namespace AcceptedConversionRuntime

/-- As `AcceptedCallRuntime.run`, at `narrow`, which returns `uint8(value)`. At
words canonical for `uint8` the call root's theorems apply in both directions
and the actual resumption returns the word; at other words the call root's
reflection applies and the actual resumption fails with the dirty-integer
reason. -/
def run : IO Unit := do
  let observed ← observe
  let narrow ← observeRow observed.fixture "narrow"
  let narrowBody ← observeNarrowBody narrow.original.function.typedBody
  for word in [Word.zero, Word.ofNatModulo 7, Word.ofNatModulo 255] do
    let ⟨canonical⟩ ← Tests.SourceCoreAcceptedFixture.observed
      (TypeSystem.FixedInteger.canonical ⟨false, .w8⟩ word.val = true) "narrow canonical word"
    let started ← observeStarted observed.fixture narrow.original.key [.word word]
    have _plan : ∃ (whole : WholeInventory observed.fixture) (selected : SelectedInventory whole narrow),
        Nonempty (AcceptedCall selected word started) := by
      obtain ⟨whole⟩ := observed.fixture.inventory observed.cache observed.wellFormed
      obtain ⟨selected⟩ := whole.select narrow
      exact ⟨whole, selected, accepted_call selected observed.calls (fun admits => ⟨observed.identity, admits⟩)
        word observed.wellFormed started observed.callableProfile narrowBody.parts.inputs narrowBody.binderScheme
        (narrow_source selected narrowBody word canonical)⟩
    let result ← started.call.checkpoint.resumeWithReceipt runOptions.executionFuel runOptions.outputValidationFuel
    match result.val with
    | .succeeded returned =>
      unless returned.value == .word word do throw (IO.userError "accepted conversion output changed")
    | _ => throw (IO.userError "accepted conversion did not succeed")
  for word in [Word.ofNatModulo 256, Word.maximum] do
    let started ← observeStarted observed.fixture narrow.original.key [.word word]
    have _plan : ∃ (whole : WholeInventory observed.fixture) (selected : SelectedInventory whole narrow),
        Nonempty (AcceptedReflection selected word started) := by
      obtain ⟨whole⟩ := observed.fixture.inventory observed.cache observed.wellFormed
      obtain ⟨selected⟩ := whole.select narrow
      exact ⟨whole, selected, accepted_reflection selected observed.calls word observed.wellFormed started
        observed.callableProfile narrowBody.parts.inputs narrowBody.binderScheme⟩
    let result ← started.call.checkpoint.resumeWithReceipt runOptions.executionFuel runOptions.outputValidationFuel
    match result.val with
    | .failed reason _ =>
      unless reason == SourceCorePanics.dirtyReason do throw (IO.userError "accepted conversion failure changed")
    | _ => throw (IO.userError "accepted conversion of a dirty word did not fail")
  IO.println "ACCEPTED_CONVERSION_PUBLIC_PASS"

end AcceptedConversionRuntime

namespace AcceptedRepresentationRuntime

/-- As `AcceptedConversionRuntime.run`, at `roundTrip`, which returns
`Typedef.rep(uint8(value))`: at words canonical for `uint8` both directions
apply and the actual call returns the word; at other words the reflection
applies and the actual call fails with the dirty-integer reason. -/
def run : IO Unit := do
  let observed ← observe
  let roundTrip ← observeRow observed.fixture "roundTrip"
  let roundTripBody ← observeRoundTripBody roundTrip.original.function.typedBody
  for word in [Word.zero, Word.ofNatModulo 7, Word.ofNatModulo 255] do
    let ⟨canonical⟩ ← Tests.SourceCoreAcceptedFixture.observed
      (TypeSystem.FixedInteger.canonical ⟨false, .w8⟩ word.val = true) "roundTrip canonical word"
    let started ← observeStarted observed.fixture roundTrip.original.key [.word word]
    have _plan : ∃ (whole : WholeInventory observed.fixture) (selected : SelectedInventory whole roundTrip),
        Nonempty (AcceptedCall selected word started) := by
      obtain ⟨whole⟩ := observed.fixture.inventory observed.cache observed.wellFormed
      obtain ⟨selected⟩ := whole.select roundTrip
      exact ⟨whole, selected, accepted_call selected observed.calls (fun admits => ⟨observed.identity, admits⟩)
        word observed.wellFormed started observed.callableProfile roundTripBody.parts.inputs
        roundTripBody.binderScheme (roundTrip_source selected roundTripBody word canonical)⟩
    let result ← started.call.checkpoint.resumeWithReceipt runOptions.executionFuel runOptions.outputValidationFuel
    match result.val with
    | .succeeded returned =>
      unless returned.value == .word word do throw (IO.userError "accepted representation output changed")
    | _ => throw (IO.userError "accepted representation did not succeed")
  for word in [Word.ofNatModulo 256, Word.maximum] do
    let started ← observeStarted observed.fixture roundTrip.original.key [.word word]
    have _plan : ∃ (whole : WholeInventory observed.fixture) (selected : SelectedInventory whole roundTrip),
        Nonempty (AcceptedReflection selected word started) := by
      obtain ⟨whole⟩ := observed.fixture.inventory observed.cache observed.wellFormed
      obtain ⟨selected⟩ := whole.select roundTrip
      exact ⟨whole, selected, accepted_reflection selected observed.calls word observed.wellFormed started
        observed.callableProfile roundTripBody.parts.inputs roundTripBody.binderScheme⟩
    let result ← started.call.checkpoint.resumeWithReceipt runOptions.executionFuel runOptions.outputValidationFuel
    match result.val with
    | .failed reason _ =>
      unless reason == SourceCorePanics.dirtyReason do
        throw (IO.userError "accepted representation failure changed")
    | _ => throw (IO.userError "accepted representation of a dirty word did not fail")
  IO.println "ACCEPTED_REPRESENTATION_PUBLIC_PASS"

end AcceptedRepresentationRuntime

namespace AcceptedFixedCompoundRuntime

/-- At `doubled`, whose body converts its `Word` parameter to a `uint8` local `x`, adds `x` to it with
the checked `+=` and returns it. The call root's reflection applies at every word. Below 128 the actual
resumption returns the sum; from 128 the `+=` panics with `0x11`; at a word that is not canonical for
`uint8` the conversion fails with the dirty-integer reason. -/
def run : IO Unit := do
  let observed ← observe
  let doubled ← observeRow observed.fixture "doubled"
  let doubledBody ← observeDoubledBody doubled.original.function.typedBody
  let cases : List (Word × Option Word) :=
    [(Word.zero, some Word.zero), (Word.ofNatModulo 7, some (Word.ofNatModulo 14)),
     (Word.ofNatModulo 127, some (Word.ofNatModulo 254)), (Word.ofNatModulo 128, none),
     (Word.ofNatModulo 255, none), (Word.ofNatModulo 256, none), (Word.maximum, none)]
  for entry in cases do
    let word := entry.1
    let sum := entry.2
    let started ← observeStarted observed.fixture doubled.original.key [.word word]
    have _plan : ∃ (whole : WholeInventory observed.fixture) (selected : SelectedInventory whole doubled),
        Nonempty (AcceptedReflection selected word started) := by
      obtain ⟨whole⟩ := observed.fixture.inventory observed.cache observed.wellFormed
      obtain ⟨selected⟩ := whole.select doubled
      exact ⟨whole, selected, accepted_reflection selected observed.calls word observed.wellFormed started
        observed.callableProfile doubledBody.parts.inputs doubledBody.binderScheme⟩
    let result ← started.call.checkpoint.resumeWithReceipt runOptions.executionFuel runOptions.outputValidationFuel
    let expectedReason :=
      if word.val < 256 then SourceCorePanics.reason SourceCorePanics.arithmetic else SourceCorePanics.dirtyReason
    match sum, result.val with
    | some value, .succeeded returned =>
      unless returned.value == .word value do throw (IO.userError "accepted fixed-width compound output changed")
    | none, .failed reason _ =>
      unless reason == expectedReason do throw (IO.userError "accepted fixed-width compound failure changed")
    | _, _ => throw (IO.userError "accepted fixed-width compound outcome changed")
  IO.println "ACCEPTED_FIXED_COMPOUND_PUBLIC_PASS"

end AcceptedFixedCompoundRuntime

namespace AcceptedFixedShiftRuntime

/-- At `shifted`, whose body converts its `Word` parameter to a `uint8` local `x`, shifts `x` left in
place by the parameter, an amount of its own type, and returns it. The call root's reflection applies
at every word. At a word canonical for `uint8` the actual resumption returns Word's shift wrapped to
eight bits; at any other word the conversion fails with the dirty-integer reason. -/
def run : IO Unit := do
  let observed ← observe
  let shifted ← observeRow observed.fixture "shifted"
  let shiftedBody ← observeShiftedBody shifted.original.function.typedBody
  let cases : List (Word × Option Word) :=
    [(Word.zero, some Word.zero), (Word.ofNatModulo 1, some (Word.ofNatModulo 2)),
     (Word.ofNatModulo 3, some (Word.ofNatModulo 24)), (Word.ofNatModulo 7, some (Word.ofNatModulo 128)),
     (Word.ofNatModulo 8, some Word.zero), (Word.ofNatModulo 255, some Word.zero),
     (Word.ofNatModulo 256, none), (Word.maximum, none)]
  for entry in cases do
    let word := entry.1
    let expected := entry.2
    let started ← observeStarted observed.fixture shifted.original.key [.word word]
    have _plan : ∃ (whole : WholeInventory observed.fixture) (selected : SelectedInventory whole shifted),
        Nonempty (AcceptedReflection selected word started) := by
      obtain ⟨whole⟩ := observed.fixture.inventory observed.cache observed.wellFormed
      obtain ⟨selected⟩ := whole.select shifted
      exact ⟨whole, selected, accepted_reflection selected observed.calls word observed.wellFormed started
        observed.callableProfile shiftedBody.parts.inputs shiftedBody.binderScheme⟩
    let result ← started.call.checkpoint.resumeWithReceipt runOptions.executionFuel runOptions.outputValidationFuel
    match expected, result.val with
    | some value, .succeeded returned =>
      unless returned.value == .word value do throw (IO.userError "accepted fixed-width shift output changed")
    | none, .failed reason _ =>
      unless reason == SourceCorePanics.dirtyReason do
        throw (IO.userError "accepted fixed-width shift failure changed")
    | _, _ => throw (IO.userError "accepted fixed-width shift outcome changed")
  IO.println "ACCEPTED_FIXED_SHIFT_PUBLIC_PASS"

end AcceptedFixedShiftRuntime

namespace AcceptedFixedBitNotRuntime

/-- At `flipped`, whose body converts its `Word` parameter to a `uint8` local `x`, applies `~` to `x` in
place and returns it. The call root's reflection applies at every word. At a word canonical for
`uint8` the actual resumption returns its complement in eight bits; at any other word the conversion
fails with the dirty-integer reason. -/
def run : IO Unit := do
  let observed ← observe
  let flipped ← observeRow observed.fixture "flipped"
  let flippedBody ← observeFlippedBody flipped.original.function.typedBody
  let cases : List (Word × Option Word) :=
    [(Word.zero, some (Word.ofNatModulo 255)), (Word.ofNatModulo 1, some (Word.ofNatModulo 254)),
     (Word.ofNatModulo 7, some (Word.ofNatModulo 248)), (Word.ofNatModulo 128, some (Word.ofNatModulo 127)),
     (Word.ofNatModulo 170, some (Word.ofNatModulo 85)), (Word.ofNatModulo 255, some Word.zero),
     (Word.ofNatModulo 256, none), (Word.maximum, none)]
  for entry in cases do
    let word := entry.1
    let expected := entry.2
    let started ← observeStarted observed.fixture flipped.original.key [.word word]
    have _plan : ∃ (whole : WholeInventory observed.fixture) (selected : SelectedInventory whole flipped),
        Nonempty (AcceptedReflection selected word started) := by
      obtain ⟨whole⟩ := observed.fixture.inventory observed.cache observed.wellFormed
      obtain ⟨selected⟩ := whole.select flipped
      exact ⟨whole, selected, accepted_reflection selected observed.calls word observed.wellFormed started
        observed.callableProfile flippedBody.parts.inputs flippedBody.binderScheme⟩
    let result ← started.call.checkpoint.resumeWithReceipt runOptions.executionFuel runOptions.outputValidationFuel
    match expected, result.val with
    | some value, .succeeded returned =>
      unless returned.value == .word value do throw (IO.userError "accepted fixed-width bit-not output changed")
    | none, .failed reason _ =>
      unless reason == SourceCorePanics.dirtyReason do
        throw (IO.userError "accepted fixed-width bit-not failure changed")
    | _, _ => throw (IO.userError "accepted fixed-width bit-not outcome changed")
  IO.println "ACCEPTED_FIXED_BIT_NOT_PUBLIC_PASS"

end AcceptedFixedBitNotRuntime

namespace AcceptedFaultRuntime

/-- The actual resumption of a fresh call failed with `expected`. -/
def failsWith {artifact : SourceCoreExecution.Artifact} (outcome : SourceCoreExecution.Outcome artifact)
    (expected : Word) (row : String) : IO Unit :=
  match outcome with
  | .failed reason _ =>
    unless reason == expected do throw (IO.userError s!"accepted fault of {row} changed")
  | _ => throw (IO.userError s!"accepted fault of {row} did not fail")

/-- At the faulting words of `narrow`, `doubled`, `shifted` and `flipped`, the
row's original Source execution faults, and the call root's failure theorem
applies at the first public call: the actual resumption fails with a token
that represents the Source fault. At a word outside `uint8` each conversion
faults with the dirty-integer reason, and at a word from 128 to 255 `doubled`'s
checked `x += x` panics with `0x11`. -/
def run : IO Unit := do
  let observed ← observe
  let dirtyWords := [Word.ofNatModulo 256, Word.maximum]
  let narrow ← observeRow observed.fixture "narrow"
  let narrowBody ← observeNarrowBody narrow.original.function.typedBody
  let ⟨narrowPlain⟩ ← Tests.SourceCoreAcceptedFixture.observed
    (CellAwareInvocationAcceptedFaultLifting.CalleesPlain narrow.original.function.typedBody) "narrow callees"
  for word in dirtyWords do
    let ⟨dirty⟩ ← Tests.SourceCoreAcceptedFixture.observed
      (TypeSystem.FixedInteger.canonical ⟨false, .w8⟩ word.val = false) "narrow dirty word"
    let started ← observeStarted observed.fixture narrow.original.key [.word word]
    have _plan : ∃ (whole : WholeInventory observed.fixture) (selected : SelectedInventory whole narrow),
        Nonempty (AcceptedFailure selected word started .dirtyHigherBitsForInteger) := by
      obtain ⟨whole⟩ := observed.fixture.inventory observed.cache observed.wellFormed
      obtain ⟨selected⟩ := whole.select narrow
      exact ⟨whole, selected, accepted_failure selected observed.calls (fun admits => ⟨observed.identity, admits⟩)
        word observed.wellFormed started observed.callableProfile narrowBody.parts.inputs narrowBody.binderScheme
        narrowPlain (identity_callees_plain whole observed.wellFormed observed.identityPlain) trivial
        (narrow_fault selected narrowBody word dirty)⟩
    let result ← started.call.checkpoint.resumeWithReceipt runOptions.executionFuel runOptions.outputValidationFuel
    failsWith result.val SourceCorePanics.dirtyReason "narrow"
  let doubled ← observeRow observed.fixture "doubled"
  let doubledBody ← observeDoubledBody doubled.original.function.typedBody
  let ⟨doubledPlain⟩ ← Tests.SourceCoreAcceptedFixture.observed
    (CellAwareInvocationAcceptedFaultLifting.CalleesPlain doubled.original.function.typedBody) "doubled callees"
  for word in dirtyWords do
    let ⟨dirty⟩ ← Tests.SourceCoreAcceptedFixture.observed
      (TypeSystem.FixedInteger.canonical ⟨false, .w8⟩ word.val = false) "doubled dirty word"
    let started ← observeStarted observed.fixture doubled.original.key [.word word]
    have _plan : ∃ (whole : WholeInventory observed.fixture) (selected : SelectedInventory whole doubled),
        Nonempty (AcceptedFailure selected word started .dirtyHigherBitsForInteger) := by
      obtain ⟨whole⟩ := observed.fixture.inventory observed.cache observed.wellFormed
      obtain ⟨selected⟩ := whole.select doubled
      exact ⟨whole, selected, accepted_failure selected observed.calls (fun admits => ⟨observed.identity, admits⟩)
        word observed.wellFormed started observed.callableProfile doubledBody.parts.inputs doubledBody.binderScheme
        doubledPlain (identity_callees_plain whole observed.wellFormed observed.identityPlain) trivial
        (initializer_fault selected doubledBody.parts.read doubledBody.parts.converted doubledBody.parts.roots
          doubledBody.parts.initializedFound doubledBody.parts.initializedForm doubledBody.targetScheme word dirty)⟩
    let result ← started.call.checkpoint.resumeWithReceipt runOptions.executionFuel runOptions.outputValidationFuel
    failsWith result.val SourceCorePanics.dirtyReason "doubled"
  for word in [Word.ofNatModulo 128, Word.ofNatModulo 255] do
    let ⟨canonical⟩ ← Tests.SourceCoreAcceptedFixture.observed
      (TypeSystem.FixedInteger.canonical ⟨false, .w8⟩ word.val = true) "doubled canonical word"
    let ⟨outside⟩ ← Tests.SourceCoreAcceptedFixture.observed
      (¬ Dynamic.FixedInRange ⟨false, .w8⟩
        (Dynamic.checkedResult .add (Dynamic.fixedValue ⟨false, .w8⟩ word) (Dynamic.fixedValue ⟨false, .w8⟩ word)))
      "doubled overflowing word"
    let started ← observeStarted observed.fixture doubled.original.key [.word word]
    have _plan : ∃ (whole : WholeInventory observed.fixture) (selected : SelectedInventory whole doubled),
        Nonempty (AcceptedFailure selected word started (.panic 0x11)) := by
      obtain ⟨whole⟩ := observed.fixture.inventory observed.cache observed.wellFormed
      obtain ⟨selected⟩ := whole.select doubled
      obtain ⟨_finalContext, sourceFault⟩ := doubled_panic selected doubledBody
        ((SelectedCompilationNamedSupport.Support.of_program observed.wellFormed).certified selected.packet.header)
        word canonical outside
      exact ⟨whole, selected, accepted_failure selected observed.calls (fun admits => ⟨observed.identity, admits⟩)
        word observed.wellFormed started observed.callableProfile doubledBody.parts.inputs doubledBody.binderScheme
        doubledPlain (identity_callees_plain whole observed.wellFormed observed.identityPlain) trivial sourceFault⟩
    let result ← started.call.checkpoint.resumeWithReceipt runOptions.executionFuel runOptions.outputValidationFuel
    failsWith result.val (SourceCorePanics.reason SourceCorePanics.arithmetic) "doubled"
  let shifted ← observeRow observed.fixture "shifted"
  let shiftedBody ← observeShiftedBody shifted.original.function.typedBody
  let ⟨shiftedPlain⟩ ← Tests.SourceCoreAcceptedFixture.observed
    (CellAwareInvocationAcceptedFaultLifting.CalleesPlain shifted.original.function.typedBody) "shifted callees"
  for word in dirtyWords do
    let ⟨dirty⟩ ← Tests.SourceCoreAcceptedFixture.observed
      (TypeSystem.FixedInteger.canonical ⟨false, .w8⟩ word.val = false) "shifted dirty word"
    let started ← observeStarted observed.fixture shifted.original.key [.word word]
    have _plan : ∃ (whole : WholeInventory observed.fixture) (selected : SelectedInventory whole shifted),
        Nonempty (AcceptedFailure selected word started .dirtyHigherBitsForInteger) := by
      obtain ⟨whole⟩ := observed.fixture.inventory observed.cache observed.wellFormed
      obtain ⟨selected⟩ := whole.select shifted
      exact ⟨whole, selected, accepted_failure selected observed.calls (fun admits => ⟨observed.identity, admits⟩)
        word observed.wellFormed started observed.callableProfile shiftedBody.parts.inputs shiftedBody.binderScheme
        shiftedPlain (identity_callees_plain whole observed.wellFormed observed.identityPlain) trivial
        (initializer_fault selected shiftedBody.parts.read shiftedBody.parts.converted shiftedBody.parts.roots
          shiftedBody.parts.initializedFound shiftedBody.parts.initializedForm shiftedBody.targetScheme word dirty)⟩
    let result ← started.call.checkpoint.resumeWithReceipt runOptions.executionFuel runOptions.outputValidationFuel
    failsWith result.val SourceCorePanics.dirtyReason "shifted"
  let flipped ← observeRow observed.fixture "flipped"
  let flippedBody ← observeFlippedBody flipped.original.function.typedBody
  let ⟨flippedPlain⟩ ← Tests.SourceCoreAcceptedFixture.observed
    (CellAwareInvocationAcceptedFaultLifting.CalleesPlain flipped.original.function.typedBody) "flipped callees"
  for word in dirtyWords do
    let ⟨dirty⟩ ← Tests.SourceCoreAcceptedFixture.observed
      (TypeSystem.FixedInteger.canonical ⟨false, .w8⟩ word.val = false) "flipped dirty word"
    let started ← observeStarted observed.fixture flipped.original.key [.word word]
    have _plan : ∃ (whole : WholeInventory observed.fixture) (selected : SelectedInventory whole flipped),
        Nonempty (AcceptedFailure selected word started .dirtyHigherBitsForInteger) := by
      obtain ⟨whole⟩ := observed.fixture.inventory observed.cache observed.wellFormed
      obtain ⟨selected⟩ := whole.select flipped
      exact ⟨whole, selected, accepted_failure selected observed.calls (fun admits => ⟨observed.identity, admits⟩)
        word observed.wellFormed started observed.callableProfile flippedBody.parts.inputs flippedBody.binderScheme
        flippedPlain (identity_callees_plain whole observed.wellFormed observed.identityPlain) trivial
        (initializer_fault selected flippedBody.parts.read flippedBody.parts.converted flippedBody.parts.roots
          flippedBody.parts.initializedFound flippedBody.parts.initializedForm flippedBody.targetScheme word dirty)⟩
    let result ← started.call.checkpoint.resumeWithReceipt runOptions.executionFuel runOptions.outputValidationFuel
    failsWith result.val SourceCorePanics.dirtyReason "flipped"
  IO.println "ACCEPTED_FAULT_PUBLIC_PASS"

end AcceptedFaultRuntime

namespace AcceptedArrayRuntime

/-- The actual resumption returned the word `expected`, or failed with the panic of code `expected`. -/
def expect {artifact : SourceCoreExecution.Artifact} (outcome : SourceCoreExecution.Outcome artifact)
    (expected : Except UInt8 Word) (row : String) : IO Unit :=
  match expected, outcome with
  | .ok value, .succeeded returned =>
    unless returned.value == .word value do throw (IO.userError s!"accepted array output of {row} changed")
  | .error code, .failed reason _ =>
    unless reason == SourceCorePanics.reason code do throw (IO.userError s!"accepted array panic of {row} changed")
  | _, _ => throw (IO.userError s!"accepted array outcome of {row} changed")

/-- At `filled`, `Length.length(new Word[](uint256(value)))`: below `2^251 − 1` the actual resumption returns the
length, and from it `new` panics with `0x41`. The call root's reflection applies at every word. -/
def runFilled (observed : Observed) : IO Unit := do
  let filled ← observeRow observed.fixture "filled"
  let filledBody ← observeFilledBody filled.original.function.typedBody
  let cases : List (Word × Except UInt8 Word) :=
    [(Word.zero, .ok Word.zero), (Word.ofNatModulo 3, .ok (Word.ofNatModulo 3)),
     (Word.ofNatModulo (2 ^ 251 - 2), .ok (Word.ofNatModulo (2 ^ 251 - 2))),
     (Word.ofNatModulo (2 ^ 251 - 1), .error SourceCorePanics.allocation),
     (Word.maximum, .error SourceCorePanics.allocation)]
  for entry in cases do
    let started ← observeStarted observed.fixture filled.original.key [.word entry.1]
    have _plan : ∃ (whole : WholeInventory observed.fixture) (selected : SelectedInventory whole filled),
        Nonempty (AcceptedReflection selected entry.1 started) := by
      obtain ⟨whole⟩ := observed.fixture.inventory observed.cache observed.wellFormed
      obtain ⟨selected⟩ := whole.select filled
      exact ⟨whole, selected, accepted_reflection selected observed.calls entry.1 observed.wellFormed started
        observed.callableProfile filledBody.parts.inputs filledBody.binderScheme⟩
    let result ← started.call.checkpoint.resumeWithReceipt runOptions.executionFuel runOptions.outputValidationFuel
    expect result.val entry.2 "filled"

/-- At `listed`, `[value, value, value][value]`: below 3 the actual resumption returns the element, the parameter, and
from 3 the read panics with `0x32`. The call root's reflection applies at every word. -/
def runListed (observed : Observed) : IO Unit := do
  let listed ← observeRow observed.fixture "listed"
  let listedBody ← observeListedBody listed.original.function.typedBody
  let cases : List (Word × Except UInt8 Word) :=
    [(Word.zero, .ok Word.zero), (Word.ofNatModulo 2, .ok (Word.ofNatModulo 2)),
     (Word.ofNatModulo 3, .error SourceCorePanics.outOfBounds),
     (Word.ofNatModulo 7, .error SourceCorePanics.outOfBounds)]
  for entry in cases do
    let started ← observeStarted observed.fixture listed.original.key [.word entry.1]
    have _plan : ∃ (whole : WholeInventory observed.fixture) (selected : SelectedInventory whole listed),
        Nonempty (AcceptedReflection selected entry.1 started) := by
      obtain ⟨whole⟩ := observed.fixture.inventory observed.cache observed.wellFormed
      obtain ⟨selected⟩ := whole.select listed
      exact ⟨whole, selected, accepted_reflection selected observed.calls entry.1 observed.wellFormed started
        observed.callableProfile listedBody.parts.inputs listedBody.binderScheme⟩
    let result ← started.call.checkpoint.resumeWithReceipt runOptions.executionFuel runOptions.outputValidationFuel
    expect result.val entry.2 "listed"

/-- At `sliced`, `[value, value, value][uint256(value):][value]`: below 2 the read through the slice returns the
parameter, from 2 it is outside the slice, and from 4 the slice's start is outside the array, each `0x32`. The call root's reflection applies at every word. -/
def runSliced (observed : Observed) : IO Unit := do
  let sliced ← observeRow observed.fixture "sliced"
  let slicedBody ← observeSlicedBody sliced.original.function.typedBody
  let cases : List (Word × Except UInt8 Word) :=
    [(Word.zero, .ok Word.zero), (Word.ofNatModulo 1, .ok (Word.ofNatModulo 1)),
     (Word.ofNatModulo 2, .error SourceCorePanics.outOfBounds),
     (Word.ofNatModulo 3, .error SourceCorePanics.outOfBounds),
     (Word.ofNatModulo 4, .error SourceCorePanics.outOfBounds)]
  for entry in cases do
    let started ← observeStarted observed.fixture sliced.original.key [.word entry.1]
    have _plan : ∃ (whole : WholeInventory observed.fixture) (selected : SelectedInventory whole sliced),
        Nonempty (AcceptedReflection selected entry.1 started) := by
      obtain ⟨whole⟩ := observed.fixture.inventory observed.cache observed.wellFormed
      obtain ⟨selected⟩ := whole.select sliced
      exact ⟨whole, selected, accepted_reflection selected observed.calls entry.1 observed.wellFormed started
        observed.callableProfile slicedBody.parts.inputs slicedBody.binderScheme⟩
    let result ← started.call.checkpoint.resumeWithReceipt runOptions.executionFuel runOptions.outputValidationFuel
    expect result.val entry.2 "sliced"

/-- At `copied`, `toArray([value, value, value][:])[value]`: below 3 the read of the copy returns the parameter, and
from 3 it panics with `0x32`. The call root's reflection applies at every word. -/
def runCopied (observed : Observed) : IO Unit := do
  let copied ← observeRow observed.fixture "copied"
  let copiedBody ← observeCopiedBody copied.original.function.typedBody
  let cases : List (Word × Except UInt8 Word) :=
    [(Word.zero, .ok Word.zero), (Word.ofNatModulo 2, .ok (Word.ofNatModulo 2)),
     (Word.ofNatModulo 3, .error SourceCorePanics.outOfBounds)]
  for entry in cases do
    let started ← observeStarted observed.fixture copied.original.key [.word entry.1]
    have _plan : ∃ (whole : WholeInventory observed.fixture) (selected : SelectedInventory whole copied),
        Nonempty (AcceptedReflection selected entry.1 started) := by
      obtain ⟨whole⟩ := observed.fixture.inventory observed.cache observed.wellFormed
      obtain ⟨selected⟩ := whole.select copied
      exact ⟨whole, selected, accepted_reflection selected observed.calls entry.1 observed.wellFormed started
        observed.callableProfile copiedBody.parts.inputs copiedBody.binderScheme⟩
    let result ← started.call.checkpoint.resumeWithReceipt runOptions.executionFuel runOptions.outputValidationFuel
    expect result.val entry.2 "copied"

/-- At `referenced`, `CanStore.store(lidx(a, value), value)` then `CanStore.load(lidx(a, value))` on the literal
`a`: below 3 the actual resumption returns the stored parameter, and from 3 the store's `lidx` panics with
`0x32`. The call root's reflection applies at every word. -/
def runReferenced (observed : Observed) : IO Unit := do
  let referenced ← observeRow observed.fixture "referenced"
  let referencedBody ← observeReferencedBody referenced.original.function.typedBody
  let cases : List (Word × Except UInt8 Word) :=
    [(Word.zero, .ok Word.zero), (Word.ofNatModulo 2, .ok (Word.ofNatModulo 2)),
     (Word.ofNatModulo 3, .error SourceCorePanics.outOfBounds),
     (Word.ofNatModulo 7, .error SourceCorePanics.outOfBounds)]
  for entry in cases do
    let started ← observeStarted observed.fixture referenced.original.key [.word entry.1]
    have _plan : ∃ (whole : WholeInventory observed.fixture) (selected : SelectedInventory whole referenced),
        Nonempty (AcceptedReflection selected entry.1 started) := by
      obtain ⟨whole⟩ := observed.fixture.inventory observed.cache observed.wellFormed
      obtain ⟨selected⟩ := whole.select referenced
      exact ⟨whole, selected, accepted_reflection selected observed.calls entry.1 observed.wellFormed started
        observed.callableProfile referencedBody.parts.inputs referencedBody.binderScheme⟩
    let result ← started.call.checkpoint.resumeWithReceipt runOptions.executionFuel runOptions.outputValidationFuel
    expect result.val entry.2 "referenced"

/-- At `bumped`, `a[value] = value`, `a[value] += value` and `a[value] ~=;` on the literal `a`, then the return of
`a[value]`: below 3 the actual resumption returns the complement of twice the parameter, and from 3 the first
write's index is outside the array and panics with `0x32`. The call root's reflection applies at every word. -/
def runBumped (observed : Observed) : IO Unit := do
  let bumped ← observeRow observed.fixture "bumped"
  let bumpedBody ← observeBumpedBody bumped.original.function.typedBody
  let cases : List (Word × Except UInt8 Word) :=
    [(Word.zero, .ok Word.zero.bitNot), (Word.ofNatModulo 1, .ok (Word.ofNatModulo 2).bitNot),
     (Word.ofNatModulo 2, .ok (Word.ofNatModulo 4).bitNot),
     (Word.ofNatModulo 3, .error SourceCorePanics.outOfBounds),
     (Word.ofNatModulo 7, .error SourceCorePanics.outOfBounds)]
  for entry in cases do
    let started ← observeStarted observed.fixture bumped.original.key [.word entry.1]
    have _plan : ∃ (whole : WholeInventory observed.fixture) (selected : SelectedInventory whole bumped),
        Nonempty (AcceptedReflection selected entry.1 started) := by
      obtain ⟨whole⟩ := observed.fixture.inventory observed.cache observed.wellFormed
      obtain ⟨selected⟩ := whole.select bumped
      exact ⟨whole, selected, accepted_reflection selected observed.calls entry.1 observed.wellFormed started
        observed.callableProfile bumpedBody.parts.inputs bumpedBody.binderScheme⟩
    let result ← started.call.checkpoint.resumeWithReceipt runOptions.executionFuel runOptions.outputValidationFuel
    expect result.val entry.2 "bumped"

/-- The memory array rows `filled`, `listed`, `sliced`, `copied`, `referenced` and `bumped`. -/
def run : IO Unit := do
  let observed ← observe
  runFilled observed
  runListed observed
  runSliced observed
  runCopied observed
  runReferenced observed
  runBumped observed
  IO.println "ACCEPTED_ARRAY_PUBLIC_PASS"

end AcceptedArrayRuntime

end Tests.SourceCoreAcceptedOneCall
end
