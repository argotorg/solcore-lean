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
place; `tailed`'s body is `identity(value)` as its final value. Runtime checks place every
expression node of the nine rows among the nested sites that call `identity`'s
instantiation or their callees, and each statement list in the supported
shape. With the complete inventory the rows make a family and give
the admitted callee's static receipts. The original Source executions of
`relay`, `twice`, `tailed`, `narrow` and `roundTrip` (at words canonical for `uint8`) are lifted to
staged traces, and the call root's theorems apply at the first public call of
each in both directions: the actual resumption succeeds, and actual native
completion reconstructs a staged Source execution. At other words the call
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

Main declarations: `Tests.SourceCoreAcceptedOneCall.relay_source`,
`Tests.SourceCoreAcceptedOneCall.twice_source`,
`Tests.SourceCoreAcceptedOneCall.tailed_source`,
`Tests.SourceCoreAcceptedOneCall.narrow_source`,
`Tests.SourceCoreAcceptedOneCall.roundTrip_source`,
`Tests.SourceCoreAcceptedOneCall.narrow_fault`,
`Tests.SourceCoreAcceptedOneCall.initializer_fault`,
`Tests.SourceCoreAcceptedOneCall.doubled_panic`,
`Tests.SourceCoreAcceptedOneCall.accepted_call`,
`Tests.SourceCoreAcceptedOneCall.accepted_reflection`,
`Tests.SourceCoreAcceptedOneCall.accepted_failure` and the runtime checks
`Tests.SourceCoreAcceptedOneCall.AcceptedCallRuntime.run`,
`Tests.SourceCoreAcceptedOneCall.AcceptedNestedCallRuntime.run`,
`Tests.SourceCoreAcceptedOneCall.AcceptedTailRuntime.run`,
`Tests.SourceCoreAcceptedOneCall.AcceptedConversionRuntime.run`,
`Tests.SourceCoreAcceptedOneCall.AcceptedRepresentationRuntime.run`,
`Tests.SourceCoreAcceptedOneCall.AcceptedFixedCompoundRuntime.run`,
`Tests.SourceCoreAcceptedOneCall.AcceptedFixedShiftRuntime.run`,
`Tests.SourceCoreAcceptedOneCall.AcceptedFixedBitNotRuntime.run` and
`Tests.SourceCoreAcceptedOneCall.AcceptedFaultRuntime.run`.
-/

section
/-! The program and the declarative typing of its nine functions, constructed
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
    "function identity(value: Word) returns (Word) { return value; }",
    "function relay(value: Word) returns (Word) { return identity(value); }",
    "function twice(value: Word) returns (Word) { return identity(identity(value)); }",
    "function narrow(value: Word) returns (uint8) { return uint8(value); }",
    "function roundTrip(value: Word) returns (Word) { return Typedef.rep(uint8(value)); }",
    "function doubled(value: Word) returns (uint8) { let x: uint8 = uint8(value); x += x; return x; }",
    "function shifted(value: Word) returns (uint8) { let x: uint8 = uint8(value); x <<= value; return x; }",
    "function flipped(value: Word) returns (uint8) { let x: uint8 = uint8(value); x ~=; return x; }",
    "function tailed(value: Word) returns (Word) { identity(value) }" ]}] }

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
      shiftedFunction, flippedFunction, tailedFunction],
    [identitySignature, relaySignature, twiceSignature, narrowSignature, roundTripSignature, doubledSignature,
      shiftedSignature, flippedSignature, tailedSignature] =>
    let identityShape ← Tests.SourceCoreOperatorCalls.observeIdentity identityFunction identitySignature
    let relayShape ← observeRelay relayFunction relaySignature identitySignature
    let twiceShape ← observeTwice twiceFunction twiceSignature identitySignature
    let narrowShape ← observeNarrow narrowFunction narrowSignature
    let roundTripShape ← observeRoundTrip roundTripFunction roundTripSignature
    let doubledShape ← observeDoubled doubledFunction doubledSignature
    let shiftedShape ← observeShifted shiftedFunction shiftedSignature
    let flippedShape ← observeFlipped flippedFunction flippedSignature
    let tailedShape ← observeTailed tailedFunction tailedSignature identitySignature
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
    let ⟨distinct⟩ ← observed ((program.signatures.functions.map (·.id)).Nodup) "calls distinct signatures"
    let deep : CheckedProgramBodiesHaveStatementTyping program options.checkingFuel := {
      functions := by
        intro actual member candidate candidateMember accepted
        have declared := checkFunctionBody_success_declaration accepted
        have selects : ∀ {signature}, signature ∈ program.signatures.functions →
            actual.declaration = signature.id → candidate = signature := fun signatureMember same =>
          signature_of_id distinct candidateMember signatureMember (declared.symm.trans same)
        simp only [functions, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
      methods := by intro method member; simp only [methods, List.not_mem_nil] at member }
    return ⟨programWellFormed_ofCheckProgram_statements checked deep⟩
  | _, _ => throw (IO.userError "calls declaration count")

end Tests.SourceCoreAcceptedOneCall
end

section
/-! The cache rows of the nine functions and their original Source
executions: `identity` returns its parameter, `relay` returns the direct call
of `identity` with its parameter, `twice` returns the direct call of
`identity` with that call, `tailed` ends in the direct call of `identity` with
its parameter as its final value, `narrow` returns the conversion of its parameter,
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

end Tests.SourceCoreAcceptedOneCall
end

section
/-! The accepted-body public theorems at the call root. Runtime checks place
every expression node of the nine rows among the nested sites or their callees
and each statement list in the supported shape; the complete inventory turns
them into the rows of a family and gives the admitted callee's static
receipts. The original Source executions of `relay`, `twice`, `tailed`, `narrow` and
`roundTrip`, whose calls run `identity`'s body instance, are lifted through the checked
shapes, and with the existing start receipts the call root's theorems apply at
the first public call of each in both directions. The call root's reflection
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
    selected.packet.header.unique (whole.callees calls wellFormed admitted) (calls.header_shape selected.packet)
    sourceTrace
  obtain ⟨_capture, _value, _finalStore, _finalMap, _finalWorld, requiredExecution, requiredOutput, _result, output⟩ :=
    CellAwarePublicAcceptedCallForward.first_value_selected callableProfile initial.issued prepared
      selected.packet.aligned fixture.ready diagnostic support start.selected (owner fixture.recipe.compiled)
      initial.caller.base.val initial.globalReference initial.keyPhysical initial.caller.physical initial.stable
      initial.heapTyped initial.argumentsTyped bodySelected artifact checked body covered initial.represented
      initial.heaps rfl start.started start.atCheckpoint
      (congrArg SourceCoreCompatibleValues.Context.registry initial.contextAt) initial.exportsReady allocated trace
      (CellAwarePublicAcceptedCallRoot.expressions_of_family callableProfile initial.issued prepared
        selected.packet.aligned diagnostic support artifact checked closed ports wellFormed rows size)
  obtain ⟨_capture, value, finalStore, _finalMap, _finalWorld, required, run, _result⟩ :=
    CellAwarePublicAcceptedCallRoot.checkpoint_has_sufficient_fuel_selected callableProfile initial.issued prepared
      selected.packet.aligned fixture.ready diagnostic support start.selected (owner fixture.recipe.compiled)
      initial.caller.base.val initial.globalReference initial.keyPhysical initial.caller.physical initial.stable
      initial.heapTyped initial.argumentsTyped bodySelected artifact checked body covered initial.represented
      initial.heaps rfl start.started allocated trace
      (CellAwarePublicAcceptedCallRoot.expressions_of_family callableProfile initial.issued prepared
        selected.packet.aligned diagnostic support artifact checked closed ports wellFormed rows size)
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
          selected.packet.aligned diagnostic support artifact checked closed ports wellFormed rows)
    exact ⟨sidecar, size, environment, bound, finalContext, outcome, after, allocated, staged, result⟩

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
        selected.packet.aligned diagnostic support artifact checked closed ports wellFormed rows)
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
        selected.packet.aligned diagnostic support artifact checked closed ports wellFormed rows size)
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

end Tests.SourceCoreAcceptedOneCall
end
