import Solcore.Test.Frontend.Source.Inference
import Solcore.Test.SourceSemantics.CompiledOrigins
import Solcore.Test.SourceSemantics.CoreLowering.Generalized.Export
import Solcore.Test.SourceSemantics.CoreLowering.Selected.Faulting
import Solcore.Test.SourceSemantics.CoreLowering.Generalized.Body
import Solcore.Test.SourceSemantics.CoreLowering.Mixed.Reads
import Solcore.Test.SourceSemantics.CoreLowering.Mixed.Operators
import Solcore.Test.SourceSemantics.CoreLowering.Mixed.Control
import Solcore.Test.SourceSemantics.CoreLowering.Mixed.Loops
import Solcore.Test.SourceSemantics.CoreLowering.Selected.Generalized
import Solcore.Test.SourceSemantics.CoreLowering.Selected.Interleaved
import Solcore.Test.SourceSemantics.CoreLowering.Selected.ProfilesControl
import Solcore.Test.SourceSemantics.CoreLowering.Selected.Profiles
import Solcore.Test.SourceSemantics.CoreLowering.Selected.Projected
import Solcore.Test.SourceSemantics.CoreLowering.LexicalFailureForward
import Solcore.Test.SourceSemantics.CoreLowering.Selected.OperatorAlias
import Solcore.Test.SourceSemantics.CoreLowering.Method.OriginEvidence
import Solcore.Test.SourceSemantics.CoreLowering.Foundations.Execution
import Solcore.Test.SourceSemantics.CoreLowering.Constructor
import Solcore.Test.SourceSemantics.CoreLowering.Canonical.Scoped
import Solcore.Test.SourceSemantics.CoreLowering.Recursive.Index
import Solcore.Test.SourceSemantics.CoreLowering.Closed.Admitted
import Solcore.Test.SourceSemantics.CoreLowering.Foundations.Heaps
import Solcore.Test.SourceSemantics.CoreLowering.Closed.Owned
import Solcore.Test.SourceSemantics.CoreLowering.Compatible.Payloads
import Solcore.Test.SourceSemantics.CoreLowering.Compatible.Encoding
import Solcore.Test.SourceSemantics.CoreLowering.Data.Places
import Solcore.Test.SourceSemantics.CoreLowering.Foundations.Stages
import Solcore.Test.SourceSemantics.CoreLowering.Callable.Paired
import Solcore.Test.Core.DataAndCells
import Solcore.Test.SourceSemantics.CoreLowering.Foundations.Statements
import Solcore.Test.SourceSemantics.CoreLowering.Data.Values
import Solcore.Test.Frontend.Source.Compiler
import Solcore.Test.SourceSemantics.Inference
import Solcore.Test.SourceSemantics.CoreLowering.Compatible.General
import Solcore.Test.SourceSemantics.CoreLowering.Compatible.Matches
import Solcore.Test.SourceSemantics.CoreLowering.Callable.Ancestry
import Solcore.Test.SourceSemantics.CoreLowering.Callable.Indexed
import Solcore.Test.SourceSemantics.CoreLowering.Compatible.Statements
import Solcore.Test.SourceSemantics.CoreLowering.Compatible.Ambient
import Solcore.Test.SourceSemantics.CoreLowering.UnifiedCorpus
import Solcore.Test.SourceSemantics.CoreLowering.UnifiedOperatorCorpus
import Solcore.Test.SourceSemantics.CoreLowering.Compatible.Expressions
import Solcore.Test.SourceSemantics.CoreLowering.TypedStatements
import Solcore.Test.SourceSemantics.CoreLowering.Named.Operators
import Solcore.Test.SourceSemantics.CoreLowering.Builtin
import Solcore.Test.SourceSemantics.CoreLowering.Recursive.Stages
import Solcore.Test.SourceSemantics.CoreLowering.Callable.LambdaViews
import Solcore.Test.SourceSemantics.CoreLowering.Callable.IndexedLambda
import Solcore.Test.SourceSemantics.CoreLowering.Protected
import Solcore.Test.SourceSemantics.CoreLowering.Foundations.ReachableDiagnostics
import Solcore.Test.SourceSemantics.CoreLowering.Named.Loops
import Solcore.Test.SourceSemantics.CoreLowering.Recursive.NamedCatalog
import Solcore.Test.SourceSemantics.CoreLowering.Callable.Coercion
import Solcore.Test.SourceSemantics.CoreLowering.Recursive.NamedStatements
import Solcore.Test.SourceSemantics.CoreLowering.Recursive.NamedHeaders
import Solcore.Test.SourceSemantics.CoreLowering.Recursive.NamedExpressions
import Solcore.Test.SourceSemantics.CoreLowering.Recursive.NamedPublic
import Solcore.Test.SourceSemantics.Semantics
import Solcore.Test.SourceSemantics.IntegerBitNot
import Solcore
import Solcore.Test.TypeSystem.Inference
import Solcore.Test.SourceSemantics.SemanticsSubstitution
import Solcore.Test.SourceSemantics.SemanticsBoundary
import Solcore.SourceSemantics.CoreLowering
import Solcore.Test.Resolved.Semantics
import Solcore.Test.Frontend.PublicBoundary
import Solcore.Test.Frontend.Programs
import Solcore.Test.Frontend.LocalExpressions
import Solcore.Test.Frontend.WordOperators
import Solcore.Test.Core.LocalFragments
import Solcore.Test.Frontend.RuntimeValues
import Solcore.Test.Frontend.RuntimeParameters
import Solcore.Test.Frontend.ReturnBodies
import Solcore.Test.Frontend.RuntimeFunctions
import Solcore.Test.Frontend.LocalFunctions
import Solcore.Test.Frontend.TerminalBodies
import Solcore.Test.Frontend.ComputationOwners
import Solcore.Test.Frontend.TerminalTreeRunner
import Solcore.Test.Frontend.TerminalTreeInvariance
import Solcore.Test.Frontend.RecursiveRuntimeEntries
import Solcore.Test.Frontend.TypedLetBodies
import Solcore.Test.Frontend.TypedLetBodyRunner
import Solcore.Test.Frontend.TypedLetBodyStore
import Solcore.Test.Frontend.TypedLetTrees.Trees
import Solcore.Test.Frontend.TypedLetTrees.Evaluation
import Solcore.Test.Frontend.TypedLetTrees.Runner
import Solcore.Test.Frontend.TypedLetTrees.Store
import Solcore.Test.Frontend.TypedLetTrees.Owner
import Solcore.Test.Frontend.TypedLetTrees.TypeExtension
import Solcore.Test.Frontend.RecursiveTypedLetEntries
import Solcore.Test.Frontend.TypedLetTrees.Evaluator
import Solcore.Test.Frontend.TypedLetTrees.RawOwner
import Solcore.Test.Frontend.MatchCounts
import Solcore.Test.Frontend.StructuralForms
import Solcore.Test.Frontend.RecursiveComputations
import Solcore.Test.Frontend.RecursiveFunctions
import Solcore.Test.Frontend.RecursiveConditionals
import Solcore.Test.Frontend.RecursiveUnary
import Solcore.Test.Frontend.RecursiveLazy
import Solcore.Test.Frontend.RecursiveEntries
import Solcore.Test.Frontend.ComputationRuntime
import Solcore.Test.Frontend.ExpectedLambdas
import Solcore.Test.Frontend.LocalApplicationGroups
import Solcore.Test.Frontend.GroupedConditionals
import Solcore.Test.Frontend.DeepGroupedConditionals
import Solcore.Test.Frontend.ClosedSourceBodies
import Solcore.Test.Frontend.ClosedSourceData
import Solcore.Test.Frontend.ExpectedDataImages
import Solcore.Test.Frontend.ExpectedPairedBridges
import Solcore.Test.Frontend.ClosedStrictWords
import Solcore.Test.Frontend.SymbolicDepth
import Solcore.Test.Frontend.LambdaDepth
import Solcore.Test.Frontend.OwnerExpressions
import Solcore.Test.Syntax.Declarations
import Solcore.Test.Syntax.CoreBlocks
import Solcore.Test.Syntax.LexerAndTrivia
import Solcore.Test.Syntax.ExpressionsAndPatterns
import Solcore.Test.Syntax.ModulesAndImports
import Solcore.Test.Syntax.Diagnostics
import Solcore.Test.Syntax.Statements
import Solcore.Test.Syntax.Recovery
import Solcore.Test.Syntax.CanonicalTraces
import Solcore.Test.Syntax.PublicBoundary
import Solcore.Test.Syntax.Pragmas
import Solcore.Test.Syntax.ExpressionAtoms
import Solcore.Test.Syntax.Types
import Solcore.Test.Syntax.Parameters
import Solcore.Test.Syntax.Yul
import Solcore.Syntax.Parser.LeftAssociativeTraceStateProperties
import Solcore.Syntax.Parser.LeftAssociativeTraceCompletenessProperties
import Solcore.Syntax.Parser.LeftAssociativeUnrestrictedFuelContractProperties
import Solcore.Test.Abi.StaticWord
import Solcore.Test.Core.Primitives
import Solcore.Test.SourceSemantics.CoreLowering.Foundations.EntryPoints
import Solcore.Test.Core.Wire
import Solcore.Test.SourceSemantics.CoreLowering.Captured.Nested
import Solcore.Test.SourceSemantics.CoreLowering.Captured.Locals
import Solcore.Test.SourceSemantics.CoreLowering.Captured.Assignments
import Solcore.Test.SourceSemantics.CoreLowering.Direct.Calls
import Solcore.Test.SourceSemantics.CoreLowering.Captured.Mappings
import Solcore.Test.SourceSemantics.CoreLowering.LexicalFailure
import Solcore.Test.SourceSemantics.CoreLowering.Captured.Branches
import Solcore.Test.SourceSemantics.CoreLowering.Named.Branches
import Solcore.Test.SourceSemantics.CoreLowering.Captured.Loops
import Solcore.Test.SourceSemantics.CoreLowering.OperatorCalls
import Solcore.Test.SourceSemantics.CoreLowering.ClosureDirect
import Solcore.Test.SourceSemantics.CoreLowering.Canonical.Formation
import Solcore.Test.SourceSemantics.CoreLowering.Recursive.Formation
import Solcore.Test.SourceSemantics.CoreLowering.GenericDirect
import Solcore.Test.SourceSemantics.CoreLowering.Evidence.Direct
import Solcore.Test.SourceSemantics.CoreLowering.Foundations.Snapshots
import Solcore.Test.SourceSemantics.CoreLowering.Evidence.Closure
import Solcore.Test.ContractRuntime.ContractCalls
import Solcore.Test.ContractRuntime.HostDriver
import Solcore.Test.Core.HostMachine
import Solcore.Test.ContractRuntime.WorldState
import Solcore.Test.ContractRuntime.AddressSelectedHost
import Solcore.Test.ContractRuntime.TopLevelExecution
import Solcore.Test.ContractRuntime.SelectedExecution
import Solcore.Test.ContractRuntime.Frames
import Solcore.Test.ContractRuntime.ValueCalls
import Solcore.Test.ContractRuntime.Creation
import Solcore.Test.ContractRuntime.NestedExecution
import Solcore.Test.ContractRuntime.Logs
import Solcore.Test.ContractRuntime.ParentIndexedFrames
import Solcore.Test.Synthesis.Generators
import Solcore.Test.Synthesis.Scalars
import Solcore.Test.Synthesis.Loops
import Solcore.Test.Synthesis.Enums
import Solcore.Test.Synthesis.Traits
import Solcore.Test.Synthesis.Memory
import Solcore.Test.Synthesis.EventsAndReverts
import Solcore.Test.Synthesis.Arrays
import Solcore.Test.Synthesis.CallGraphs
import Solcore.Test.Synthesis.Aggregates
import Solcore.Test.Synthesis.Storage
import Solcore.Test.Frontend.Source.Specialization
import Solcore.Test.Frontend.Source.Staged
import Solcore.Test.Frontend.Source.CompilationPlan
import Solcore.Test.SourceSemantics.CoreLowering.Direct.Linking
import Solcore.Test.Frontend.Source.TypedRuntime
import Solcore.Test.Frontend.Source.StagedIntegers
import Solcore.Test.SourceSemantics.CoreLowering.Callable.Prepared




import Solcore.Test.SourceSemantics.CoreLowering.Chosen.Admission
import Solcore.Test.SourceSemantics.CoreLowering.Chosen.Bodies
import Solcore.Test.SourceSemantics.CoreLowering.Chosen.OuterBodies
import Solcore.Test.SourceSemantics.CoreLowering.Chosen.PublicOutcomes
import Solcore.Test.SourceSemantics.CoreLowering.NestedFormation
import Solcore.Test.SourceSemantics.CoreLowering.Evidence.Scoped
import Solcore.Test.SourceSemantics.CoreLowering.Method.PublicSequences
import Solcore.Test.SourceSemantics.CoreLowering.CoercionPublic
import Solcore.Test.Frontend.RustHull.Runtime
import Solcore.Test.Frontend.RustHull.YulPrimitives
import Solcore.Test.Frontend.RustHull.Effects
import Solcore.Test.Frontend.RustHull.Correspondence
import Solcore.Test.Frontend.RustHull.Accounts
import Solcore.Test.Frontend.RustHull.Creation
import Solcore.Test.Frontend.RustHull.Calls
import Solcore.Frontend.RustHull.Safety
import Solcore.Test.Synthesis.SourceMeaning
import Solcore.Test.Synthesis.Malformed
import Solcore.Test.Synthesis.Bytes
import Solcore.Test.Synthesis.Calls
import Solcore.Test.SourceCallReturnGolden
set_option autoImplicit false

open Solcore
open Solcore.Core

namespace Tests

def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do
    throw (IO.userError message)

def isError {ε α : Type} : Except ε α → Bool
  | .error _ => true
  | .ok _ => false

def coreConditionalProgram : Program := {
  resultType := .bool
  body :=
    .letE
      (.bool true)
      (.ifE (.var 0) (.bool false) (.bool true))
}

def testSemanticCore : IO Unit := do
  assertTrue coreConditionalProgram.check
    "the closed let/if Core witness must type-check"
  assertTrue (coreConditionalProgram.run 6 == .outOfFuel)
    "six CEK transitions must be insufficient for the seven-step witness"
  assertTrue (coreConditionalProgram.run 7 == .done (.bool false))
    "the Core evaluator must finish exactly at the seven-transition boundary"
  for fuel in [0, 1, 2, 3, 4, 5, 6, 7, 8] do
    match coreConditionalProgram.run fuel with
    | .fault error =>
        throw (IO.userError s!"well-typed Core program faulted: {reprStr error}")
    | _ => pure ()
  let lazyBranchProgram : Program := {
    resultType := .bool
    body := .ifE (.bool true) (.bool false) (.var 99)
  }
  assertTrue (lazyBranchProgram.run 3 == .outOfFuel)
    "three CEK transitions must stop before the selected branch returns"
  assertTrue (lazyBranchProgram.run 4 == .done (.bool false))
    "if must evaluate only the selected branch"
  let nearestBindingProgram : Program := {
    resultType := .bool
    body :=
      .letE
        (.bool true)
        (.letE
          (.bool false)
          (.ifE (.var 0) (.bool false) (.var 1)))
  }
  assertTrue nearestBindingProgram.check
    "nested de Bruijn bindings must type-check"
  assertTrue (nearestBindingProgram.run 16 == .done (.bool true))
    "index 0 must be the nearest binding and index 1 the next outer binding"
  let openProgram : Program := {
    resultType := .bool
    body := .var 0
  }
  assertTrue (!openProgram.check)
    "an unbound de Bruijn index must be rejected statically"
  let nonBooleanCondition : Program := {
    resultType := .bool
    body := .ifE .unit (.bool true) (.bool false)
  }
  assertTrue (!nonBooleanCondition.check)
    "if conditions must have bool type"
  assertTrue (nonBooleanCondition.run 2 == .fault (.expectedBool .unit))
    "the unchecked machine must expose a non-bool condition as a fault"
  let branchMismatch : Program := {
    resultType := .bool
    body := .ifE (.bool true) .unit (.bool false)
  }
  assertTrue (!branchMismatch.check)
    "if branches must have the same type"
  let declaredResultMismatch : Program := {
    resultType := .unit
    body := .bool true
  }
  assertTrue (!declaredResultMismatch.check)
    "the inferred Core result must equal the declared result type"
  assertTrue (Word.ofNat? 42).isSome
    "an in-range word literal must construct a Core word"
  assertTrue (Word.ofNat? wordModulus).isNone
    "a Core word must reject the first out-of-range natural"

def testPrimitiveAlgebra : IO Unit := do
  let word (value : Nat) : IO Word :=
    match Word.ofNat? value with
    | some result => pure result
    | none => throw (IO.userError s!"{value} must be an in-range Core word")
  let one ← word 1
  let two ← word 2
  let three ← word 3
  let seven ← word 7
  let shift0 ← word 0
  let shift255 ← word 255
  let shift256 ← word 256
  let doubledMaximum ← word (wordModulus - 2)
  let highBit ← word (2 ^ 255)
  assertTrue (Word.maximum.add one == Word.zero)
    "word addition must wrap modulo 2^256"
  assertTrue (Word.zero.sub one == Word.maximum)
    "word subtraction must wrap modulo 2^256"
  assertTrue (Word.maximum.mul two == doubledMaximum)
    "word multiplication must wrap modulo 2^256"
  assertTrue (seven.udiv three == two)
    "word division must use the unsigned quotient"
  assertTrue (seven.udiv Word.zero == Word.zero)
    "word division by zero must return zero"
  assertTrue (seven.umod three == one)
    "word modulo must use the unsigned remainder"
  assertTrue (seven.umod Word.zero == Word.zero)
    "word modulo by zero must return zero"
  assertTrue (Word.maximum.bitAnd Word.zero == Word.zero)
    "word bitwise and must operate on 256 bits"
  assertTrue (Word.maximum.bitOr Word.zero == Word.maximum)
    "word bitwise or must operate on 256 bits"
  assertTrue (Word.maximum.bitXor Word.maximum == Word.zero)
    "word bitwise xor must operate on 256 bits"
  assertTrue (Word.zero.bitNot == Word.maximum)
    "word bitwise not must complement exactly 256 bits"
  assertTrue (one.shiftLeft shift0 == one)
    "word left shift by zero must preserve the value"
  assertTrue (one.shiftLeft shift255 == highBit)
    "word left shift by 255 must retain the high bit"
  assertTrue (one.shiftLeft shift256 == Word.zero)
    "word left shift by 256 must return zero"
  assertTrue (one.shiftLeft Word.maximum == Word.zero)
    "word left shift by the maximum word must return zero"
  assertTrue (Word.maximum.shiftRight shift0 == Word.maximum)
    "word right shift by zero must preserve the value"
  assertTrue (Word.maximum.shiftRight shift255 == one)
    "logical word right shift by 255 must retain the low bit"
  assertTrue (Word.maximum.shiftRight shift256 == Word.zero)
    "word right shift by 256 must return zero"
  assertTrue (Word.maximum.shiftRight Word.maximum == Word.zero)
    "word right shift by the maximum word must return zero"
  assertTrue
    (UnaryOp.boolNot.apply (.bool true) == some (.bool false))
    "boolNot must negate a boolean"
  assertTrue
    (UnaryOp.boolNot.apply (.word one) == none)
    "an unchecked unary primitive must reject an invalid operand"
  assertTrue
    (BinaryOp.wordEq.apply (.word one) (.word one) == some (.bool true))
    "wordEq must return a Core boolean"
  assertTrue
    (BinaryOp.wordEq.apply (.word Word.zero) (.word Word.maximum) ==
      some (.bool false))
    "wordEq must distinguish the minimum and maximum words"
  assertTrue
    (BinaryOp.wordEq.apply (.word Word.maximum) (.word Word.maximum) ==
      some (.bool true))
    "wordEq must identify equal maximum words"
  assertTrue
    (BinaryOp.wordGt.apply (.word two) (.word one) == some (.bool true))
    "wordGt must compare words as unsigned values"
  assertTrue
    (BinaryOp.wordGt.apply (.word Word.maximum) (.word Word.zero) ==
      some (.bool true))
    "wordGt must order the maximum word above zero"
  assertTrue
    (BinaryOp.wordGt.apply (.word Word.zero) (.word Word.maximum) ==
      some (.bool false))
    "wordGt must not order zero above the maximum word"
  assertTrue
    (BinaryOp.wordAdd.apply (.bool true) (.word one) == none)
    "an unchecked binary primitive must reject invalid operands"

def testM1cKernel : IO Unit := do
  let one ←
    match Word.ofNat? 1 with
    | some value => pure value
    | none => throw (IO.userError "one must be an in-range Core word")
  let addWrap : Program := {
    resultType := .word
    body := .binary .wordAdd (.word Word.maximum) (.word one)
  }
  assertTrue addWrap.check
    "a wordAdd expression with word operands must type-check"
  assertTrue (addWrap.run 4 == .outOfFuel)
    "four CEK transitions must be insufficient for a binary literal expression"
  assertTrue (addWrap.run 5 == .done (.word Word.zero))
    "wordAdd must complete exactly at its five-transition boundary"
  let negated : Program := {
    resultType := .bool
    body := .unary .boolNot (.bool true)
  }
  assertTrue negated.check
    "a boolNot expression with a bool operand must type-check"
  assertTrue (negated.run 2 == .outOfFuel)
    "two CEK transitions must be insufficient for a unary literal expression"
  assertTrue (negated.run 3 == .done (.bool false))
    "boolNot must complete exactly at its three-transition boundary"
  let derivedLessThan : Program := {
    resultType := .bool
    body := Expr.wordLt (.word Word.zero) (.word one)
  }
  assertTrue derivedLessThan.check
    "the derived wordLt combinator must type-check"
  assertTrue (derivedLessThan.run 11 == .done (.bool true))
    "wordLt must bind operands in source order before applying wordGt"
  let derivedLtLeftFaultsFirst : Program := {
    resultType := .bool
    body := Expr.wordLt (.var 11) (.var 22)
  }
  assertTrue
    (derivedLtLeftFaultsFirst.run 1 == .fault (.unboundVariable 11))
    "wordLt must preserve left-to-right operand fault order"
  let derivedGeLeftFaultsFirst : Program := {
    resultType := .bool
    body := Expr.wordGe (.var 11) (.var 22)
  }
  assertTrue
    (derivedGeLeftFaultsFirst.run 2 == .fault (.unboundVariable 11))
    "wordGe must preserve left-to-right operand fault order"
  let derivedComparisonsAvoidCapture : Program := {
    resultType := .bool
    body :=
      .letE (.word one)
        (.ifE
          (Expr.wordLt (.word Word.zero) (.var 0))
          (Expr.wordGe (.word Word.zero) (.var 0))
          (.bool true))
  }
  assertTrue derivedComparisonsAvoidCapture.check
    "derived swapped comparisons must preserve free de Bruijn references"
  assertTrue (derivedComparisonsAvoidCapture.run 30 == .done (.bool false))
    "wordLt and wordGe must weaken the right operand before binding the left"
  let leftFaultsFirst : Program := {
    resultType := .word
    body := .binary .wordAdd (.var 11) (.var 22)
  }
  assertTrue
    (leftFaultsFirst.run 1 == .fault (.unboundVariable 11))
    "the unchecked binary machine must evaluate the left operand first"
  let rightBeforeInvalidApplication : Program := {
    resultType := .word
    body := .binary .wordAdd .unit (.var 22)
  }
  assertTrue
    (rightBeforeInvalidApplication.run 3 == .fault (.unboundVariable 22))
    "the unchecked binary machine must evaluate the right operand before applying the operator"
  let invalidUnary : Program := {
    resultType := .bool
    body := .unary .boolNot .unit
  }
  assertTrue
    (invalidUnary.run 2 == .fault (.invalidUnaryOperand .boolNot .unit))
    "the unchecked machine must expose an invalid unary operand"

def assertCheckError
    (name : String)
    (program : Program)
    (code : CheckErrorCode)
    (path : CheckPath) :
    IO CheckError := do
  match program.checkDetailed with
  | .ok type =>
      throw (IO.userError s!"{name} unexpectedly checked as {reprStr type}")
  | .error error =>
      assertTrue (error.code == code)
        s!"{name} returned {error.codeName}, expected {code.name}"
      assertTrue (error.path == path)
        s!"{name} returned path {reprStr error.path}, expected {reprStr path}"
      pure error

def testDetailedCoreChecker : IO Unit := do
  let unbound : Program := {
    resultType := .bool
    body :=
      .letE (.bool true)
        (.ifE (.bool true) (.var 2) (.bool false))
  }
  let unboundError ←
    assertCheckError "unbound variable" unbound .unboundVariable
      [.letBody, .ifThen]
  assertTrue (unboundError.data == .unboundVariable 2 1)
    "unbound-variable diagnostic arguments changed"
  let expectedBool : Program := {
    resultType := .bool
    body := .ifE .unit (.bool true) (.bool false)
  }
  let expectedBoolError ←
    assertCheckError "non-bool condition" expectedBool .expectedBool
      [.ifCondition]
  assertTrue (expectedBoolError.data == .expectedBool .unit)
    "expected-bool diagnostic arguments changed"
  let branchMismatch : Program := {
    resultType := .bool
    body := .ifE (.bool true) .unit (.bool false)
  }
  let branchError ←
    assertCheckError "branch type mismatch" branchMismatch .branchTypeMismatch
      [.ifElse]
  assertTrue (branchError.data == .branchTypeMismatch .unit .bool)
    "branch-mismatch diagnostic arguments changed"
  let resultMismatch : Program := {
    resultType := .unit
    body := .bool true
  }
  let resultError ←
    assertCheckError "declared result mismatch" resultMismatch
      .declaredResultTypeMismatch []
  assertTrue
    (resultError.data == .declaredResultTypeMismatch .unit .bool)
    "declared-result-mismatch diagnostic arguments changed"
  let unaryMismatch : Program := {
    resultType := .bool
    body := .unary .boolNot .unit
  }
  let unaryError ←
    assertCheckError "unary operand mismatch" unaryMismatch
      .primitiveOperandTypeMismatch [.unaryOperand]
  assertTrue
    (unaryError.data == .primitiveOperandTypeMismatch .bool .unit)
    "unary primitive diagnostic arguments changed"
  let binaryLeftMismatch : Program := {
    resultType := .word
    body := .binary .wordAdd (.bool true) (.var 99)
  }
  let binaryLeftError ←
    assertCheckError "binary left operand mismatch" binaryLeftMismatch
      .primitiveOperandTypeMismatch [.binaryLeft]
  assertTrue
    (binaryLeftError.data == .primitiveOperandTypeMismatch .word .bool)
    "binary-left primitive diagnostic arguments changed"
  let binaryRightMismatch : Program := {
    resultType := .word
    body := .binary .wordAdd (.word Word.zero) (.bool true)
  }
  let binaryRightError ←
    assertCheckError "binary right operand mismatch" binaryRightMismatch
      .primitiveOperandTypeMismatch [.binaryRight]
  assertTrue
    (binaryRightError.data == .primitiveOperandTypeMismatch .word .bool)
    "binary-right primitive diagnostic arguments changed"

def expectCanonicalWorkspacePath
    (text : String) : IO Solcore.Workspace.CanonicalSourcePath :=
  match Solcore.Workspace.CanonicalSourcePath.parse text with
  | some path => pure path
  | none =>
      throw (IO.userError s!"{reprStr text} must be a canonical workspace path")

def expectExternalLibraryName
    (text : String) : IO Solcore.Workspace.ExternalLibraryName :=
  match Solcore.Workspace.ExternalLibraryName.parse text with
  | some name => pure name
  | none =>
      throw (IO.userError s!"{reprStr text} must be an external library name")

def testWorkspacePathIdentity : IO Unit := do
  let acceptedPaths := [
    "a.sol",
    "A0_b.sol",
    "a/B2_c.sol",
    "function.sol",
    "a.solc",
    "A0_b.solc",
    "a/B2_c.solc",
    "function.solc"
  ]
  for text in acceptedPaths do
    let path ← expectCanonicalWorkspacePath text
    assertTrue (path.render == text)
      s!"canonical workspace path changed during rendering: {reprStr text}"
    assertTrue
      (Solcore.Workspace.CanonicalSourcePath.parse path.render == some path)
      s!"rendered workspace path did not parse: {reprStr text}"
  let nulPath := "a" ++ String.singleton (Char.ofNat 0) ++ "b.solc"
  let rejectedPaths := [
    "",
    "/a.solc",
    ".solc",
    "a/.solc",
    "a//b.solc",
    "a/./b.solc",
    "a/../b.solc",
    "a\\b.solc",
    "a:b.solc",
    nulPath,
    "λ.solc",
    "a.SOL",
    "a.sol.sol",
    "a.solc.sol",
    "a.sol.solc",
    "a.sol?query",
    "a.sol#fragment",
    "a.SOLC",
    "a.solc.solc",
    "a.solc?query",
    "a.solc#fragment",
    "a%2Fb.solc",
    "a/",
    "a/.solc/",
    "1a.solc",
    "_a.solc"
  ]
  for text in rejectedPaths do
    assertTrue
      (Solcore.Workspace.CanonicalSourcePath.parse text).isNone
      s!"invalid workspace path was accepted: {reprStr text}"
  let acceptedNames := ["A", "a0_b", "function"]
  for text in acceptedNames do
    let name ← expectExternalLibraryName text
    assertTrue (name.render == text)
      s!"external library name changed during rendering: {reprStr text}"
    assertTrue
      (Solcore.Workspace.ExternalLibraryName.parse name.render == some name)
      s!"rendered external library name did not parse: {reprStr text}"
  let nulName := "a" ++ String.singleton (Char.ofNat 0)
  let rejectedNames := [
    "", "lib.core", "lib/core", "λ", "lib-name", "1lib", "_lib", nulName
  ]
  for text in rejectedNames do
    assertTrue
      (Solcore.Workspace.ExternalLibraryName.parse text).isNone
      s!"invalid external library name was accepted: {reprStr text}"
  let sharedPath ← expectCanonicalWorkspacePath "Shared.solc"
  let otherPath ← expectCanonicalWorkspacePath "Other.solc"
  let externalName ← expectExternalLibraryName "Alpha"
  let mainId : Solcore.Workspace.SourceId := {
    library := .main
    path := sharedPath
  }
  let standardId : Solcore.Workspace.SourceId := {
    library := .standard
    path := sharedPath
  }
  let externalId : Solcore.Workspace.SourceId := {
    library := .external externalName
    path := sharedPath
  }
  let otherMainId : Solcore.Workspace.SourceId := {
    library := .main
    path := otherPath
  }
  assertTrue
    (mainId != standardId && mainId != externalId &&
      standardId != externalId && mainId != otherMainId)
    "structured source identities must retain library and path distinctions"
  let mainModuleId := Solcore.Workspace.SourceId.toModuleId mainId
  let standardModuleId := Solcore.Workspace.SourceId.toModuleId standardId
  let externalModuleId := Solcore.Workspace.SourceId.toModuleId externalId
  let otherMainModuleId := Solcore.Workspace.SourceId.toModuleId otherMainId
  assertTrue
    (mainModuleId != standardModuleId &&
      mainModuleId != externalModuleId &&
      mainModuleId != otherMainModuleId &&
      standardModuleId != externalModuleId &&
      standardModuleId != otherMainModuleId &&
      externalModuleId != otherMainModuleId)
    "source-to-module conversion must not merge distinct source identities"

def canonicalWorkspaceFixture : Solcore.Workspace.RawWorkspace := {
  entry := "Main.solc"
  mainSources := [
    { path := "Zed.solc", content := "z" },
    { path := "Main.solc", content := "λ🙂" },
    { path := "Alpha/Util.solc", content := "" }
  ]
  externalLibraries := [
    {
      name := "zeta"
      sources := [
        { path := "Z.solc", content := "zz" },
        { path := "A.solc", content := "a" }
      ]
    },
    { name := "Empty", sources := [] },
    {
      name := "Alpha"
      sources := [
        { path := "Nested/Z.solc", content := "nested" },
        { path := "A.solc", content := "α" }
      ]
    }
  ]
}

def permutedCanonicalWorkspaceFixture : Solcore.Workspace.RawWorkspace := {
  entry := "Main.solc"
  mainSources := [
    { path := "Alpha/Util.solc", content := "" },
    { path := "Zed.solc", content := "z" },
    { path := "Main.solc", content := "λ🙂" }
  ]
  externalLibraries := [
    {
      name := "Alpha"
      sources := [
        { path := "A.solc", content := "α" },
        { path := "Nested/Z.solc", content := "nested" }
      ]
    },
    {
      name := "zeta"
      sources := [
        { path := "A.solc", content := "a" },
        { path := "Z.solc", content := "zz" }
      ]
    },
    { name := "Empty", sources := [] }
  ]
}

def testWorkspaceCanonicalValidation : IO Unit := do
  let raw := canonicalWorkspaceFixture
  assertTrue ("λ🙂".utf8ByteSize == 6)
    "the multibyte workspace fixture must occupy six UTF-8 bytes"
  assertTrue (raw.sourceFiles == 7)
    "raw workspace sourceFiles must count every source occurrence"
  assertTrue (raw.sourceBytes == 18)
    "raw workspace sourceBytes must count exact UTF-8 content bytes"
  let mainPath ← expectCanonicalWorkspacePath "Main.solc"
  let alphaUtilPath ← expectCanonicalWorkspacePath "Alpha/Util.solc"
  let zedPath ← expectCanonicalWorkspacePath "Zed.solc"
  let aPath ← expectCanonicalWorkspacePath "A.solc"
  let nestedPath ← expectCanonicalWorkspacePath "Nested/Z.solc"
  let externalZPath ← expectCanonicalWorkspacePath "Z.solc"
  let alphaName ← expectExternalLibraryName "Alpha"
  let emptyName ← expectExternalLibraryName "Empty"
  let zetaName ← expectExternalLibraryName "zeta"
  let expectedEntry : Solcore.Workspace.SourceId := {
    library := .main
    path := mainPath
  }
  let expectedFiles : List Solcore.Workspace.WorkspaceFile := [
    {
      id := { library := .main, path := alphaUtilPath }
      content := ""
    },
    {
      id := expectedEntry
      content := "λ🙂"
    },
    {
      id := { library := .main, path := zedPath }
      content := "z"
    },
    {
      id := { library := .external alphaName, path := aPath }
      content := "α"
    },
    {
      id := { library := .external alphaName, path := nestedPath }
      content := "nested"
    },
    {
      id := { library := .external zetaName, path := aPath }
      content := "a"
    },
    {
      id := { library := .external zetaName, path := externalZPath }
      content := "zz"
    }
  ]
  match Solcore.Workspace.validate raw with
  | .error errors =>
      throw (IO.userError
        s!"canonical workspace was rejected: {reprStr errors}")
  | .ok workspace =>
      assertTrue (workspace.entry == expectedEntry)
        "validated workspace entry must be the structured main source identity"
      assertTrue
        (workspace.declaredExternalLibraries == [alphaName, emptyName, zetaName])
        "validated workspace must retain empty libraries in canonical order"
      assertTrue (workspace.files == expectedFiles)
        "validated workspace files or contents differ from canonical order"
      assertTrue (workspace.sourceFiles == 7)
        "validated sourceFiles must preserve the raw occurrence count"
      assertTrue (workspace.sourceBytes == 18)
        "validated sourceBytes must preserve exact UTF-8 content bytes"
      assertTrue
        (workspace.lookupSource expectedEntry == expectedFiles[1]?)
        "entry lookup must return the exact canonical entry source"
      let externalId : Solcore.Workspace.SourceId := {
        library := .external alphaName
        path := nestedPath
      }
      assertTrue
        (workspace.lookupSource externalId == expectedFiles[4]?)
        "external lookup must return the exact structured source"
      assertTrue
        (workspace.declaredExternalLibraries.contains alphaName)
        "every external lookup target must retain its library declaration"
      for file in workspace.files do
        match file.id.library with
        | .external name =>
            assertTrue (workspace.declaredExternalLibraries.contains name)
              "every validated external source must name a declared library"
        | _ => pure ()
      let absentId : Solcore.Workspace.SourceId := {
        library := .external emptyName
        path := aPath
      }
      assertTrue (workspace.lookupSource absentId).isNone
        "an empty declared library must not synthesize a source"

def testWorkspaceEqualContentIdentity : IO Unit := do
  let raw : Solcore.Workspace.RawWorkspace := {
    entry := "Shared.solc"
    mainSources := [{ path := "Shared.solc", content := "same source text" }]
    externalLibraries := [{
      name := "Lib"
      sources := [{ path := "Shared.solc", content := "same source text" }]
    }]
  }
  let sharedPath ← expectCanonicalWorkspacePath "Shared.solc"
  let libName ← expectExternalLibraryName "Lib"
  let mainId : Solcore.Workspace.SourceId := {
    library := .main
    path := sharedPath
  }
  let externalId : Solcore.Workspace.SourceId := {
    library := .external libName
    path := sharedPath
  }
  assertTrue (mainId != externalId)
    "equal source paths in different libraries must have distinct identities"
  match Solcore.Workspace.validate raw with
  | .error errors =>
      throw (IO.userError
        s!"equal-content identity fixture was rejected: {reprStr errors}")
  | .ok workspace =>
      match workspace.lookupSource mainId, workspace.lookupSource externalId with
      | some mainFile, some externalFile =>
          assertTrue
            (mainFile.id == mainId && externalFile.id == externalId)
            "validation must retain both structured source identities"
          assertTrue
            (mainFile.content == "same source text" &&
              externalFile.content == "same source text" &&
              mainFile.content == externalFile.content)
            "validation must retain equal content under distinct source identities"
      | _, _ =>
          throw (IO.userError
            "validation did not retain both equal-content sources")

def workspaceAllErrorsFixture : Solcore.Workspace.RawWorkspace := {
  entry := "bad.entry"
  mainSources := [
    { path := "z-path", content := "z" },
    { path := "A-path", content := "first" },
    { path := "A-path", content := "second" },
    { path := "Dup.solc", content := "first" },
    { path := "Dup.solc", content := "second" }
  ]
  externalLibraries := [
    {
      name := "bad-name"
      sources := [
        { path := "z:path", content := "z" },
        { path := "A:path", content := "first" },
        { path := "A:path", content := "second" }
      ]
    },
    { name := "bad-name", sources := [] },
    {
      name := "Lib"
      sources := [
        { path := "Dup.solc", content := "first" },
        { path := "Dup.solc", content := "second" }
      ]
    }
  ]
}

def testWorkspaceValidationErrors : IO Unit := do
  let duplicatePath ← expectCanonicalWorkspacePath "Dup.solc"
  let libName ← expectExternalLibraryName "Lib"
  let expected : List Solcore.Workspace.ValidationError := [
    .invalidEntryPath "bad.entry",
    .invalidExternalLibraryName "bad-name",
    .duplicateExternalLibraryName "bad-name",
    .invalidMainSourcePath "A-path",
    .invalidMainSourcePath "z-path",
    .invalidExternalSourcePath "bad-name" "A:path",
    .invalidExternalSourcePath "bad-name" "z:path",
    .duplicateMainSourcePath duplicatePath,
    .duplicateExternalSourcePath libName duplicatePath
  ]
  let actual := Solcore.Workspace.validationErrors workspaceAllErrorsFixture
  assertTrue (actual == expected)
    s!"workspace validation errors differ from canonical sorted set: {reprStr actual}"
  match Solcore.Workspace.validate workspaceAllErrorsFixture with
  | .error errors =>
      assertTrue (errors == expected)
        "workspace rejection must return the complete canonical error list"
  | .ok _ =>
      throw (IO.userError "workspace containing every structural error was accepted")
  let missingPath ← expectCanonicalWorkspacePath "Missing.solc"
  let missingFixture : Solcore.Workspace.RawWorkspace := {
    entry := "Missing.solc"
    mainSources := [{ path := "Other.solc", content := "other" }]
    externalLibraries := []
  }
  assertTrue
    (Solcore.Workspace.validationErrors missingFixture == [.missingEntry missingPath])
    "a valid absent entry must produce exactly missingEntry"
  let emptyMainFixture : Solcore.Workspace.RawWorkspace := {
    entry := "Missing.solc"
    mainSources := []
    externalLibraries := []
  }
  assertTrue
    (Solcore.Workspace.validationErrors emptyMainFixture ==
      [.missingEntry missingPath])
    "a valid entry with no main sources must produce exactly missingEntry"
  let invalidEntryFixture : Solcore.Workspace.RawWorkspace := {
    entry := "bad.entry"
    mainSources := []
    externalLibraries := []
  }
  assertTrue
    (Solcore.Workspace.validationErrors invalidEntryFixture ==
      [.invalidEntryPath "bad.entry"])
    "an invalid entry path must suppress missingEntry"
  let invalidExternalFixture : Solcore.Workspace.RawWorkspace := {
    entry := "Main.solc"
    mainSources := [{ path := "Main.solc", content := "main" }]
    externalLibraries := [{
      name := "bad-name"
      sources := [{ path := "bad:path", content := "external" }]
    }]
  }
  assertTrue
    (Solcore.Workspace.validationErrors invalidExternalFixture == [
      .invalidExternalLibraryName "bad-name",
      .invalidExternalSourcePath "bad-name" "bad:path"
    ])
    "invalid external paths must be reported under invalid library names"
  let sharedPath ← expectCanonicalWorkspacePath "Shared.solc"
  let repeatedDeclarations : Solcore.Workspace.RawWorkspace := {
    entry := "Main.solc"
    mainSources := [{ path := "Main.solc", content := "main" }]
    externalLibraries := [
      {
        name := "Lib"
        sources := [{ path := "Shared.solc", content := "first" }]
      },
      {
        name := "Lib"
        sources := [{ path := "Shared.solc", content := "second" }]
      }
    ]
  }
  assertTrue
    (Solcore.Workspace.validationErrors repeatedDeclarations == [
      .duplicateExternalLibraryName "Lib",
      .duplicateExternalSourcePath libName sharedPath
    ])
    "external duplicate paths must be detected across repeated declarations"

def assertWorkspaceValidationEqual
    (left right : Solcore.Workspace.RawWorkspace)
    (message : String) : IO Unit :=
  match Solcore.Workspace.validate left, Solcore.Workspace.validate right with
  | .error leftErrors, .error rightErrors =>
      assertTrue (leftErrors == rightErrors) message
  | .ok leftWorkspace, .ok rightWorkspace =>
      assertTrue
        (leftWorkspace.entry == rightWorkspace.entry &&
          leftWorkspace.declaredExternalLibraries ==
            rightWorkspace.declaredExternalLibraries &&
          leftWorkspace.files == rightWorkspace.files)
        message
  | _, _ => throw (IO.userError message)

def testWorkspaceValidationEquivalence : IO Unit := do
  assertWorkspaceValidationEqual
    canonicalWorkspaceFixture permutedCanonicalWorkspaceFixture
    "raw main, library, and source permutations must validate identically"
  let redistributedLeft : Solcore.Workspace.RawWorkspace := {
    entry := "Main.solc"
    mainSources := [{ path := "Main.solc", content := "main" }]
    externalLibraries := [
      {
        name := "Lib"
        sources := [
          { path := "A.solc", content := "a" },
          { path := "B.solc", content := "b" }
        ]
      },
      { name := "Lib", sources := [] }
    ]
  }
  let redistributedRight : Solcore.Workspace.RawWorkspace := {
    entry := "Main.solc"
    mainSources := [{ path := "Main.solc", content := "main" }]
    externalLibraries := [
      { name := "Lib", sources := [{ path := "B.solc", content := "b" }] },
      { name := "Lib", sources := [{ path := "A.solc", content := "a" }] }
    ]
  }
  assertTrue (redistributedLeft != redistributedRight)
    "redistribution fixture must contain different raw declaration grouping"
  assertWorkspaceValidationEqual redistributedLeft redistributedRight
    "redistributing sources across duplicate same-name declarations must preserve validation"

def staticSemanticsSpineTests : IO Unit := do
  testProgramEnvironmentAndTypeResolution
  testProgramModuleResolution
  testProgramTypeAliases
  testProgramInterfaces
  testProgramImports
  Tests.ImportedResolutionConsumers.testImportedResolutionConsumers
  testProgramLoading
  TypedTraitResolution.testTypedTraitResolution
  TraitResolutionEvidenceEquality.run
  ProgramIdentity.testProgramIdentity
  testProgramSignatures
  ExecutableImplMethods.testExecutableImplMethods
  SourceInference.testSourceInference
  SourceInferenceLocalIdentityValidation.testSourceInferenceLocalIdentityValidation
  SourceInferenceRequirementOwnershipValidation.testSourceInferenceRequirementOwnershipValidation
  SourceInferenceTemplateTrackingValidation.testSourceInferenceTemplateTrackingValidation
  SourceInferenceTemplateScopeValidation.testSourceInferenceTemplateScopeValidation
  SourcePhase7Inference.testSourcePhase7Inference
  testSourceConstructorVisibility
  SourceCoercionRanking.testSourceCoercionRanking
  SourceLiteralOverloadRanking.testSourceLiteralOverloadRanking
  SourceMultiStepCoercion.testSourceMultiStepCoercion
  SourceStructuralExpressions.testSourceStructuralExpressions
  SourceRequirementIdentity.testSourceRequirementIdentity
  SourceTypedIR.testSourceTypedIR
  SourceTypedIRInference.testSourceTypedIRInference
  SourceStageClassification.testSourceStageClassification
  SourceStagedValues.testSourceStagedValues
  SourceStagedValuesTamper.testSourceStagedValuesTamper
  SourceStagedValueCalls.testSourceStagedValueCalls
  SourceStagedValueCallsTamper.testSourceStagedValueCallsTamper
  SourceStagedRecursion.testSourceStagedRecursion
  SourceStagedRequiredOperators.testSourceStagedRequiredOperators
  SourceStagedMarkedImplMethods.testSourceStagedMarkedImplMethods
  SourceSpecialization.testSourceSpecialization
  SourceSpecializationWorklist.testSourceSpecializationWorklist
  SourceCompilationPlan.testSourceCompilationPlan
  SourceCompilationPlanLocalInstances.testSourceCompilationPlanLocalInstances
  SourceCoreElaboration.testSourceCoreElaboration
  SourceCoreDirectLinking.testSourceCoreDirectLinking
  SourceTypedRuntime.testSourceTypedRuntime
  SourceTypedRuntimeFirstClassEvidence.testSourceTypedRuntimeFirstClassEvidence
  SourceTypedRuntimeOperators.testSourceTypedRuntimeOperators
  SourceTypedRuntimeStateInteractions.testSourceTypedRuntimeStateInteractions
  ProgramChecking.testProgramChecking
  SourceProgramExecution.testSourceProgramExecution
  SourceCompiler.testSourceCompiler
  SourcePatternMatching.testSourcePatternMatching
  SourcePatternMatchingTamper.testSourcePatternMatchingTamper
  SourceStagedIntegerIntrinsics.testSourceStagedIntegerIntrinsics
  SourceStagedIntegerIntrinsicsTamper.testSourceStagedIntegerIntrinsicsTamper
  SourceStagedConditionals.testSourceStagedConditionals
  SourceStagedConditionalsTamper.testSourceStagedConditionalsTamper
  SourceStagedIntegerLocals.testSourceStagedIntegerLocals
  SourceStagedIntegerLocalsTamper.testSourceStagedIntegerLocalsTamper
  SourceStagedIntegerCalls.testSourceStagedIntegerCalls
  SourceStagedIntegerCallsTamper.testSourceStagedIntegerCallsTamper

private def coreRuntimeUnificationTests : IO Unit := do
  SourceCoreHeapMarkers.run
  SourceCoreSourceCells.run
  SourceCoreAllocationCodebook.run
  SourceCoreAllocationDiscovery.run
  SourceCoreAllocationContexts.run
  SourceCoreAllocationLayouts.run
  SourceCoreAllocationLedger.run
  SourceCoreRawMetadata.run
  SourceCoreCompatibleValues.run
  SourceCoreCompatiblePayload.run
  SourceCoreCompatibleMappings.run
  SourceCoreCompatibleEncoding.run
  SourceCoreCompatibleEqualityProofs.run
  SourceCoreCompatibleMappingProofs.run
  SourceCoreCompatibleMappingVirtualRoot.run
  SourceCoreCompatibleDataExpressions.run
  SourceCoreCompatibleDataControl.run
  SourceCoreCompatibleFunctions.run
  SourceCoreCompatiblePreparedFunctions.run
  SourceCoreCompatibleInputs.run
  SourceCoreCompatibleOutputs.run
  SourceCoreCompatibleMarkedFunctions.run
  SourceCoreCompatibleMarkedLedger.run
  SourceCoreCallableViews.run
  SourceCoreCallableViewWrappers.run
  SourceCoreCallablePrincipals.run
  SourceCoreCallableContextFrames.run
  SourceCoreCallableContextFrameProofs.run
  SourceCoreCallableContextFrameCodec.run
  SourceCoreCallableAncestry.run
  SourceCoreCallableAncestryPrograms.run
  SourceCoreCallableAncestryOutputs.run
  SourceCoreCallableAncestryMetadata.run
  SourceCoreCallableAncestryTemplates.run
  SourceCoreAncestryAllocationFrames.run
  SourceCoreCallableAncestryProfiles.run
  SourceCoreCompatibleOutputLeaves.run
  SourceCoreCallableAncestryCaptures.run
  SourceCoreCallableAncestryCache.run
  SourceCoreCallableAncestryPreparation.run
  SourceCoreCallableAncestryPrincipalHeaders.run
  SourceCoreCallableAncestryReadViews.run
  SourceCoreCallableAncestryReadRecipes.run
  SourceCoreCallableSharedHistory.run
  SourceCoreCallablePairedPrograms.run
  SourceCoreCallableAncestryPairedPreparation.run
  SourceCoreCallablePairedHeaders.run
  SourceCoreCallablePairedReadViews.run
  SourceCoreCallablePairedRestoration.run
  SourceCoreCallablePairedOutputs.run
  SourceCoreCallableIndexedFrames.run
  SourceCoreCallableIndexedPrograms.run
  SourceCoreCallableIndexedReadViews.run
  SourceCoreCallableIndexedOutputs.run
  SourceCoreCompatibleAssignment.run
  SourceCoreCompatibleStructuralFault.run
  SourceCoreCompatibleTargetFaults.run
  SourceCoreRuntimeKeyGuards.run
  SourceCoreCompatibleGetterReflection.run
  SourceCoreCompatibleAssignmentReflection.run
  SourceCoreCompatibleLowerReflection.run
  SourceCoreUnifiedRuntime.run
  SourceCoreUnifiedSourceBoundaryObservations.run
  SourceCoreUnifiedCompilation.run
  SourceCoreUnifiedControlCorpus.run
  SourceCoreUnifiedEvidenceCorpus.run
  SourceCoreUnifiedOperatorCorpus.run
  SourceCoreCompatibleBitNot.run
  SourceCoreCompatibleIntegerBitNot.run
  SourceCoreCompatibleBareBitNot.run
  SourceCoreUnifiedStagingCorpus.run
  SourceCompilerUnifiedRouting.run
  SourceCoreCompatibleExpressionReads.run
  SourceCoreCompatibleContextualReads.run
  SourceCoreCompatibleExpressionLiterals.run
  Solcore.Test.SourceCoreCallableIndexedAmbient.run
  Solcore.Test.SourceCoreCompatibleAmbientMappings.run
  SourceCoreCompatibleAmbientPaths.run
  SourceCoreCompatibleAmbientSnapshot.run
  SourceCoreCompatibleAmbientPlaceEffects.run
  SourceCoreCompatibleAmbientWriteback.run
  SourceCoreCompatibleExpressionProducts.run
  SourceCoreCompatibleExpressionPrimitives.run
  SourceCoreCompatibleExpressionConditionals.run
  SourceCoreCompatibleExpressionConstructors.run
  SourceCoreCompatibleExpressionMembers.run
  SourceCoreCompatibleStatements.run
  SourceCoreCompatibleExpressionIndices.run
  SourceCoreCompatibleExpressionRecursive.run
  SourceCoreCompatibleTypedCompositions.run
  SourceCoreCompatibleTypedExpressions.run
  SourceCoreCompatibleStatementMixed.run
  SourceCoreCompatibleStatementBindings.run
  SourceCoreCompatibleStatementInitialized.run
  SourceCoreTypedDataExpressionSequence.run
  SourceCoreCompatibleNamedBody.run
  SourceCoreCompatibleNamedParameters.run
  SourceCoreCompatibleExpressionProxies.run
  SourceCoreTypedStatements.run
  SourceCoreTypedStatementMixed.run
  SourceCoreNamedCompilationReceipt.run
  SourceCoreTypedNamedParameters.run
  SourceCoreCompatibleTypedPlaceExpressions.run
  SourceCoreCompatibleTypedAssignment.run
  SourceCoreTypedScopedStatements.run
  SourceCoreTypedScopedControl.run
  SourceCoreCompatibleTypedAssignmentFaults.run
  SourceCoreTypedMixedNamedParameters.run
  SourceCoreTypedLexicalControl.run
  SourceCoreCompatibleBareAssignment.run
  SourceCoreCompatibleRenamedAssignment.run
  SourceCoreCompatibleGeneralIndices.run
  SourceCoreCompatibleGeneralExpressions.run
  SourceCoreTypedLexicalNamedParameters.run
  SourceCoreTypedLexicalWhile.run
  SourceCoreBuiltinBodyMeaning.run
  SourceCoreBuiltinCalls.run
  SourceCoreTypedBuiltinCalls.run
  SourceCoreTypedLexicalWhileNative.run
  SourceCoreCompatibleAssignmentStatements.run
  SourceCoreNamedCalls.run
  SourceCoreRecursiveBuiltinExpressions.run
  SourceCoreCallableIndexedBuiltinValues.run
  SourceCoreTypedImperative.run
  SourceCoreNamedArguments.run
  SourceCoreCallableIndexedNamedValues.run
  SourceCoreCallableNamedCanonicalOrder.run
  SourceCoreTypedForHeader.run
  SourceCoreCallableIndexedRetainedNamedValues.run
  SourceCoreBuiltinLexicalStatements.run
  SourceCoreBuiltinAssignmentStatements.run
  SourceCoreBuiltinForHeader.run
  SourceCoreCallableIndexedLambdaValues.run
  SourceCoreTypedImperativeFor.run
  SourceCoreCompatibleRenamedBareBitNot.run
  SourceCoreBuiltinNamedCalls.run
  SourceCoreCompatiblePatternProofs.run
  SourceCoreCompatibleCompositePatterns.run
  SourceCoreCompatibleMatchArmAllocations.run
  SourceCoreCompatibleMatchPrefixes.run
  SourceCoreTypedImperativeForUnary.run
  SourceCoreCallableIndexedLambdaCalls.run
  SourceCoreCallableIndexedLambdaViewCalls.run
  SourceCoreCallableLambdaViewEdits.run
  SourceCoreCallableLambdaViewBodyTree.run
  SourceCoreProtectedNamedAssignments.run
  SourceCoreProtectedNamedLexical.run
  SourceCoreCallableLambdaViewScalarTrees.run
  SourceCoreCompatibleMatchTypedPrefixes.run
  SourceCoreProtectedNamedLexicalAssignments.run
  SourceCoreBuiltinImperativeFor.run
  SourceCoreCallableLambdaViewDataTrees.run
  SourceCoreCallableLambdaViewIndexedTrees.run
  SourceCoreCallableLambdaViewBuiltinTrees.run
  SourceCoreProtectedBareNamedAssignments.run
  SourceCoreGenericImperativeMatch.run
  SourceCoreBuiltinImperativeMatch.run
  SourceCoreCallableLambdaViewBuiltinBodyTree.run
  SourceCoreCallableLambdaViewSourceTyping.run
  SourceCoreCallableLambdaViewStaticTyping.run
  SourceCoreCallableLambdaViewSemanticReceipt.run
  SourceCoreCallableIndexedLambdaSemanticCalls.run
  SourceCoreProtectedNamedWhileEdges.run
  SourceCoreProtectedNamedWhileStatements.run
  SourceCoreProtectedWhileBodyContracts.run
  SourceCoreProtectedNamedLoops.run
  SourceCoreNamedLoopFunctionBody.run
  SourceCoreProtectedForBodyContracts.run
  SourceCoreProtectedForHeaders.run
  SourceCoreCallableIndexedLambdaGeneration.run
  SourceCoreAssignmentReachableDiagnostics.run
  SourceCoreProtectedNamedFor.run
  SourceCoreCallableIndexedLambdaScalarNativeTyping.run
  SourceCoreNamedForFunctionBody.run
  SourceCoreAssignmentDiagnosticCertificates.run
  SourceCoreCallableCallEvidence.run
  SourceCoreCatalogRegistrationPrefix.run
  SourceCoreProtectedAssignmentReachableDiagnostics.run
  SourceCoreCatalogNominalCoverage.run
  SourceCoreCallableAuthenticatedCallEvidence.run
  SourceCoreRecursiveNamedCatalog.run
  SourceCoreForHeaderReachableDiagnostics.run
  SourceCoreGeneralExpressionNativeTyping.run
  SourceCoreCallableCallEvidenceCertificates.run
  SourceCoreImperativeForReachableDiagnostics.run
  SourceCoreRecursiveBuiltinNativeTyping.run
  SourceCoreCallableCoercionSpine.run
  SourceCoreMatchReachableDiagnostics.run
  SourceCoreRecursiveNamedTraceBounds.runBounds
  SourceCoreImperativeNativePolicyTyping.run
  SourceCorePreparedMatchDiagnostics.run
  SourceCoreCallableCoercionEvidenceOrigins.run
  SourceCoreCallableIndexedLambdaImperativeNativeTyping.run
  SourceCoreNamedBodyReachableDiagnostics.run
  SourceCoreCallableCoercionPlanProvenance.run
  SourceCoreCallableIndexedCachedNativeTyping.run
  SourceCorePreparedForDiagnostics.run
  SourceCoreRecursiveNamedWhileBounds.run
  SourceCoreCallableCoercionBodyProvenance.run
  SourceCoreRecursiveNamedHeaderBounds.run
  SourceCoreCallableIndexedParameterNativeInversion.run
  SourceCoreRecursiveNamedForBounds.run
  SourceCoreCallableCoercionPreparation.run
  SourceCoreRecursiveNamedPlaceKeyBounds.run
  SourceCoreRecursiveNamedBareAssignmentBounds.run
  SourceCoreRecursiveNamedExpressionBounds.run
  SourceCoreCallableCoercionSourceSelection.run
  SourceCoreRecursiveNamedBareBitNotBounds.run
  SourceCoreRecursiveNamedExpressionCompositionsBounds.run
  SourceCoreRecursiveNamedPlaceAssignmentBounds.run
  SourceCoreCallableCoercionMethodBodyMeaning.run
  SourceCoreRecursiveNamedBuiltinBounds.run
  SourceCoreRecursiveNamedDataExpressionBounds.run
  SourceCoreRecursiveNamedAssignmentHeadBounds.run
  SourceCoreCallableCoercionPathMeaning.run
  SourceCoreRecursiveNamedExpressionTreeBounds.run
  SourceCoreRecursiveNamedProtectedHeaderBounds.run
  SourceCoreRecursiveNamedLexicalControlBounds.run
  SourceCoreCallableCoercionMethodEvidenceInvariant.run
  SourceCoreRecursiveNamedLexicalTreeBounds.run
  SourceCoreRecursiveNamedFunctionFinishBounds.run
  SourceCoreRecursiveNamedImperativeForBounds.run
  SourceCoreCallableCoercionSelectedInvocation.run
  SourceCoreRecursiveNamedCatalogBodyFinishBounds.run
  SourceCoreRecursiveNamedCatalogMutualMeaning.run
  SourceCoreCallableCoercionSourcePaths.run
  SourceCoreRecursiveNamedCatalogFiniteCompletion.run
  SourceCoreRecursiveNamedCatalogNativeContexts.run
  SourceCoreCallableCoercionExpressions.run
  SourceCoreRecursiveGlobalInitializationMeaning.run
  SourceCoreRecursiveNamedStaticExtraction.run
  SourceCoreRecursiveNamedAssignmentNativeTyping.run
  SourceCoreRecursiveNamedCatalogInitialization.run
  SourceCoreCallableCoercionRawGroups.run
  SourceCoreRecursiveNamedCachedSupport.run
  SourceCoreRecursiveNamedPreparedInitialization.run
  SourceCoreReachableStatementContinuations.run
  SourceCoreRecursiveNamedResidualContexts.run
  SourceCoreCallableCoercionRawNamedCalls.run
  SourceCoreRecursiveNamedPublicBootstrapGlobals.run
  SourceCoreCompatibleSourceInstantiationClosure.run
  SourceCoreCallableCoercionRawNamedCallAdmission.run
  SourceCoreRecursiveNamedResidualExpressions.run
  SourceCoreCallableCoercionRawNamedCallScalarArguments.run
  SourceCoreRecursiveNamedSourceSignatureFacts.run
  SourceCoreRecursiveNamedSelectedExpressions.run
  SourceCoreReachableLexicalStatements.run
  SourceCoreRecursiveNamedPreparedParameterProjections.run
  SourceCoreCallableCoercionRawNamedCallBuiltinArguments.run
  SourceCoreRecursiveNamedHeaderParameterProjections.run
  SourceCoreRecursiveNamedReachedExpressions.run
  SourceCoreReachableImperativeForStatements.run
  SourceCoreRecursiveNamedSpecializationBodyFacts.run
  SourceCoreRecursiveNamedRetainedSubstitutionFacts.run
  SourceCoreRecursiveNamedPreparedSourceFrames.run
  SourceCoreRecursiveNamedSpecializationValidity.run
  SourceCoreRecursiveNamedSpecializationStageFacts.run
  SourceCoreReachableImperativeMatchStatements.run
  SourceCoreCallableAuthenticatedNamedCalls.run
  SourceCoreRecursiveNamedMatchResidualContexts.run
  SourceCoreRecursiveNamedHeaderScopeDeclarations.run
  SourceCoreReachableMatchContinuations.run
  SourceCoreRecursiveNamedMatchPrefixBounds.run
  SourceCoreRecursiveNamedInitialContextValidity.run
  SourceCoreReachableTerminalMatchStatements.run
  SourceCoreRecursiveNamedMatchHeadBounds.run
  SourceCoreNumericLiteralEvidenceReceipts.run
  SourceCoreRecursiveNamedImperativeMatchBounds.run
  SourceCoreCompatibleLiteralRuntime.run
  SourceCoreCompatibleGeneralRuntime.run
  SourceCoreRecursiveNamedPublicRootFactory.run
  SourceCoreRecursiveNamedCatalogMatchMeaning.run
  SourceCoreTypedDefaultMatchContinuations.run
  SourceCoreRecursiveNamedPublicRootArguments.run
  SourceCoreCompatibleGeneralRuntimeExtraction.run
  SourceCoreCompatiblePatternLiteralRuntime.run
  SourceCoreRecursiveNamedImperativeMatchSyntax.run
  SourceCoreCompatiblePatternRuntime.run
  SourceCoreCompatibleMatchRuntimeSelection.run
  SourceCoreRecursiveNamedWhileRuntimeBounds.run
  SourceCoreRecursiveNamedPublicSimpleInputs.run
  SourceCoreCompatibleMatchRuntimeHead.run
  SourceCoreRecursiveNamedLexicalRuntimeBounds.run
  SourceCoreRecursiveNamedForHeaderRuntimeBounds.run
  SourceCoreRecursiveNamedForRuntimeBounds.run
  SourceCoreRecursiveNamedPublicDataInputs.run
  SourceCoreRecursiveNamedImperativeRuntimeBounds.run
  SourceCoreRecursiveNamedPreparedStageContracts.run
  SourceCoreRecursiveNamedCatalogRuntimeMutualMeaning.run
  SourceCoreRecursiveNamedPublicSpecializationMeaning.run
  SourceCoreCallableIndexedLambdaRuntimeBody.run
  SourceCoreCallableIndexedLambdaNamedRuntimeBodyMeaning.run
  SourceCoreStagedClosedEvaluationMeaning.run
  SourceCoreCallableIndexedLambdaNestedRuntimeBodyMeaning.run
  SourceCoreStagedIntegerStatementsMeaning.run
  SourceCoreCallableIndirectCallBounds.run
  SourceCoreStagedIntegerLetMeaning.run
  SourceCoreStagedIntegerResidualMeaning.run
  SourceCoreRecursiveNamedPreparedHeaderPolicies.run
  SourceRecursiveStagePrimitiveOperators.run
  SourceRecursiveStageTupleExpressions.run
  SourceCoreRecursiveStageTupleMeaning.run
  SourceCoreCallablePreparedMethodSelection.run
  SourceCoreCallablePreparedOperatorSuffixMeaning.run
  SourceCoreRecursiveNamedLambdaFormationExpressions.run
  SourceCoreRecursiveStageMappingReadMeaning.run
  SourceCoreRecursiveStageMappingTupleMeaning.run
  SourceCoreRecursiveNamedPreparedCallEvidence.run
  SourceCoreRecursiveStagePrimitiveMeaning.run
  SourceCoreGenericImperativeMatchExtraction.run
  SourceCoreCompatibleReadNativeTyping.run
  SourceCoreBuiltinImperativeMatchBody.run
  SourceCoreRecursiveNamedExpressions.run
  SourceCoreProtectedNamedPlaces.run
  SourceSemanticsIntegerBitNot.run
  SourceCoreCompatiblePlaceKeyTyping.run
  SourceCoreCompatiblePlaceOrder.run
  SourceCoreCompatibleMixedPaths.run
  SourceCoreCompatiblePathCertificates.run
  SourceCoreCompatiblePlaceSnapshot.run
  SourceCoreCompatibleHeap.run
  SourceCoreLambdaTemplates.run
  SourceCoreCompatibleHeapOutputs.run

def capturedClosureSessionTests : IO Unit := do
  SourceCoreCapturedReuse.run
  SourceCoreCapturedDirect.run
  SourceCoreCapturedPacked.runForward
  SourceCoreCapturedLocal.run
  SourceCoreCapturedCopy.run
  SourceCoreCapturedAssignment.run
  SourceCoreCapturedMapping.runInitialForward
  SourceCoreDirectFailure.run
  SourceCoreCapturedMapping.runExportError
  SourceCoreCapturedMapping.runNamedExportErrors
  SourceCoreCapturedMappingResumption.run
  SourceCoreCapturedNested.runComplete
  SourceCoreCapturedBranch.runForward
  SourceCoreNamedBranch.run
  SourceCoreCapturedWhile.runForward
  SourceCoreNamedWhile.run
  SourceCoreNamedBlock.run
  SourceCoreNamedOperators.run
  SourceCoreOperatorCalls.run
  SourceCoreNamedMatch.run
  SourceCoreCapturedMatch.runForward
  SourceCoreNamedFor.run
  SourceCoreCapturedFor.runForward
  SourceCoreConstructorCalls.runForward
  SourceCoreDirectCalls.runForward
  SourceCoreBuiltinCalls.runForward
  SourceCoreClosureDirect.runForward
  SourceCoreRecursiveIndex.runForward
  SourceCoreCanonicalScoped.runForward
  SourceCoreCanonicalFormation.runForward
  SourceCoreRecursiveFormation.runForward
  SourceCoreGenericDirect.runForward
  SourceCoreEvidenceDirect.runForward
  SourceCoreNestedFormation.runForward
  SourceCoreEvidenceScoped.runForward
  SourceCoreEvidenceClosure.runForward
  SourceCoreEvidenceMethod.runForward
  SourceCoreMethodClosure.runForward
  SourceCoreMethodScoped.runForward
  SourceCoreMethodNamedScoped.runForward
  SourceCoreMethodImplementationScoped.runForward
  SourceCoreMethodOriginEvidence.runForward
  SourceCoreMethodOriginEvidence.runForwardAt1000
  SourceCoreMethodOriginEvidence.Certified.runForward
  SourceCoreCertifiedLexicalFailure.run
  SourceCoreMethodOriginEvidence.CompilerProfile.runForward
  SourceCoreCanonicalScoped.CompilerProfile.runForward
  SourceCorePublicSourceOutcomes.run
  SourceCoreRecursiveIndex.CompilerProfile.runForward
  SourceCoreConstructorCalls.CompilerProfile.runForward
  SourceCoreCoercionPublic.runForward
  SourceCoreAcceptedBodyBindings.run
  SourceCoreFinalCatalogLateRows.runLateRows
  SourceCoreOrdinarySyntaxTable.run
  SourceCoreMethodOwnEvidence.runForward
  SourceCoreMethodGenericSubstitution.runForward
  SourceCoreMethodDirectEvidence.runForward

set_option maxRecDepth 2048 in
def run : IO Unit := do
  Tests.SourceBodyTemplateScope.main

  Tests.SourceCachedTemplateScope.main
  Tests.SourceCompiledNestedInitializerPrivacy.main

  Tests.SourceCompiledDirectCallPredicateOrigins.main
  Tests.SourceCompiledGeneralizedBarrierConnection.main

  Tests.SourceCompiledTemplateCallOrigins.main
  Tests.SourceCompiledCatalogedCallOrigins.main
  Tests.SourceCompiledTemplateCallOwner.main
  Tests.SourceSelectedTemplateInventory.main

  Tests.SourcePreparedQualifiedLocalReadBindings.main
  Tests.SourcePreparedQualifiedLocalReadOwner.main
  Tests.SourceCompiledDirectCallOrigins.main

  SourceCoreChosenOrdinaryAcceptedFixture.run
  SourceCoreChosenOrdinaryAcceptedPublicBootstrapReceipt.run
  SourceCoreChosenOrdinaryAcceptedPublicSessionEntry.run
  SourceCoreChosenOrdinaryAcceptedPublicProgramOutcome.run
  SourceCoreChosenOrdinaryAcceptedBodyMetadata.run
  SourceCoreChosenOrdinaryAcceptedTyping.run
  SourceCoreChosenOrdinaryAcceptedHeader.run
  SourceCoreChosenOrdinaryAcceptedOuterTyping.run
  SourceCoreChosenOrdinaryAcceptedStaticInventory.run
  coreLocalFragmentPairBoundaryTests
  resolvedPairBoundaryTests
  resolvedLocalSemanticsTests
  frontendParsedLocalExpressionTests
  frontendParsedWordLiteralTests
  frontendParsedWordBitwiseTests
  frontendParsedTypeNameTests
  frontendParsedRuntimeParameterTests
  frontendParsedReturnBodyTests
  frontendParsedRuntimeFunctionEntryTests
  frontendParsedRuntimeArgumentStaticTests
  frontendParsedRuntimeOwnerTests
  frontendParsedParameterDeclarationTests
  frontendParsedFunctionCompilationTests
  frontendParsedWordAdditionTests
  frontendParsedWordArithmeticTests
  frontendParsedWordGreaterTests
  frontendParsedCompiledExecutionTests
  frontendParsedCompiledObservationTests
  frontendParsedStoreIndependenceTests
  frontendParsedFuelBoundTests
  frontendParsedResumptionTests
  frontendParsedWordEqualityTests
  frontendParsedWordInequalityTests
  frontendParsedWordLessEqualTests
  frontendParsedWordLessTests
  frontendParsedWordGreaterEqualTests
  frontendParsedConditionalReturnBodiesTests
  frontendParsedTerminalReturnBodiesTests
  frontendParsedTerminalBodyInvarianceTests
  frontendParsedTerminalRuntimeEntriesTests
  frontendParsedWordDivisionTests
  frontendParsedCompilationOwnersTests
  frontendParsedParameterPositionTests
  frontendParsedParameterCompilationTests
  frontendParsedTypeTableExtensionTests
  frontendParsedTerminalReturnTreeTests
  frontendParsedTerminalReturnTreeEvaluationTests
  frontendParsedTerminalReturnTreeRunnerTests
  frontendParsedTerminalReturnTreeInvarianceTests
  frontendParsedRecursiveRuntimeEntryTests
  frontendParsedTypedLetReturnBodyTests
  frontendParsedTypedLetReturnBodyEvaluationTests
  frontendParsedTypedLetReturnBodyRunnerTests
  frontendParsedTypedLetReturnBodyStoreTests
  frontendParsedTypedLetReturnBodyOwnerTests
  frontendParsedTypedLetReturnBodyTypeExtensionTests
  frontendParsedTypedLetRuntimeEntryTests
  frontendParsedTypedLetReturnTreeTests
  frontendParsedTypedLetReturnTreeEvaluationTests
  frontendParsedTypedLetReturnTreeRunnerTests
  frontendParsedTypedLetReturnTreeStoreTests
  frontendParsedTypedLetReturnTreeOwnerTests
  frontendParsedTypedLetReturnTreeTypeExtensionTests
  frontendParsedRecursiveTypedLetRuntimeEntryTests
  frontendParsedLocalExpressionEvaluatorTests
  frontendParsedTypedLetReturnTreeEvaluatorTests
  frontendParsedRuntimeFunctionEvaluatorTests
  frontendParsedTypedLetReturnTreeRawOwnerTests
  frontendParsedRawLookupTests
  frontendParsedBinaryTupleTests
  frontendParsedBinaryTupleEntryTests
  frontendParsedUnitTests
  frontendParsedUnitEntryTests
  frontendParsedStructuralTypeTests
  frontendParsedStructuralReturnTests
  frontendParsedStructuralParameterTests
  frontendParsedStructuralParameterEntryTests
  frontendParsedStructuralLetEntryTests
  frontendParsedManyTypeTests
  frontendParsedManyTypeEntryTests
  frontendParsedManyExpressionTests
  frontendParsedManyTupleEntryTests
  frontendParsedInferredLetTests
  frontendParsedInferredLetEntryTests
  frontendParsedLocalFragmentTests
  frontendParsedLocalFragmentEntryTests
  frontendParsedDiscardStatementTests
  frontendParsedDiscardEntryTests
  frontendParsedTerminalBlockTests
  frontendParsedTerminalBlockEntryTests
  frontendParsedRuntimeParameterTypeExtensionTests
  frontendParsedRuntimeTypeExtensionEntryTests
  frontendParsedLocalFunctionApplicationTests
  frontendParsedLocalFunctionApplicationEntryTests
  frontendParsedLocalApplicationEvaluationTests
  frontendParsedLocalApplicationEvaluationEntryTests
  frontendParsedLocalApplicationRuntimeSafetyTests
  frontendParsedLocalApplicationRuntimeSafetyEntryTests
  frontendParsedLocalApplicationRunnerTests
  frontendParsedLocalApplicationRunnerEntryTests
  frontendParsedApplicationReturnBodyTests
  frontendParsedApplicationReturnBodyEntryTests
  frontendParsedRuntimeApplicationCompilationTests
  frontendParsedRuntimeApplicationEntryTests
  frontendParsedApplicationInsertionTests
  frontendParsedApplicationInsertionEntryTests
  frontendParsedLocalComputationTests
  frontendParsedLocalComputationEntryTests
  frontendParsedLocalComputationReturnTreeTests
  frontendParsedLocalComputationReturnTreeEntryTests
  frontendParsedRuntimeComputationCompilationTests
  frontendParsedRuntimeComputationEntryTests
  frontendParsedRecursiveLocalComputationTests
  frontendParsedRecursiveComputationEntryTests
  frontendParsedRecursiveComputationBodyTests
  frontendParsedRecursiveComputationBodyEffectsTests
  frontendParsedRecursiveComputationCompilationTests
  frontendParsedRecursiveComputationFunctionEntryTests
  frontendParsedRecursiveBinaryComputationTests
  frontendParsedRecursiveBinaryFunctionEntryTests
  frontendParsedRecursiveConditionalComputationTests
  frontendParsedRecursiveConditionalFunctionEntryTests
  frontendParsedRecursiveUnaryComputationTests
  frontendParsedRecursiveUnaryFunctionEntryTests
  frontendParsedRecursiveLazyMigrationTests
  frontendParsedRecursiveLazyComputationTests
  frontendParsedRecursiveLazyFunctionEntryTests
  frontendParsedRecursiveNegatedComparisonMigrationTests
  frontendParsedRecursiveNegatedComparisonTests
  frontendParsedRecursiveNegatedComparisonEntryTests
  frontendParsedRecursiveOrderedComparisonMigrationTests
  frontendParsedRecursiveOrderedComparisonTests
  frontendParsedRecursiveOrderedComparisonEntryTests
  frontendParsedRecursiveTupleMigrationTests
  frontendParsedRecursiveTupleTests
  frontendParsedRecursiveTupleEntryTests
  frontendParsedComputationRuntimeSafetyTests
  frontendParsedComputationRuntimeSafetyEntryTests
  frontendParsedRuntimeInputValidationEntryTests
  frontendParsedRuntimeArgumentConstructionEntryTests
  frontendParsedCheckpointWorldExtensionTests
  frontendParsedWordMatchEffectTests
  frontendParsedWordMatchScopeTests
  frontendParsedWildcardMatchEffectTests
  frontendParsedWildcardMatchScopeTests
  frontendParsedOptionalMatchEffectTests
  frontendParsedOptionalMatchScopeTests
  frontendParsedGroupedMatchEffectTests
  frontendParsedGroupedMatchScopeTests
  frontendParsedTypeGeneralMatchEffectTests
  frontendParsedTypeGeneralMatchScopeTests
  frontendParsedUnaryFunctionTypeTests
  frontendParsedUnaryFunctionParameterTests
  frontendParsedUnaryFunctionTypeEffectTests
  frontendParsedScopedShadowingMigrationTests
  frontendParsedScopedShadowingBoundaryTests
  frontendParsedScopedShadowingEffectTests
  frontendParsedComputationTypeTableBoundaryTests
  frontendParsedComputationTypeTableEffectTests
  frontendParsedRecursiveIdentityEffectTests
  frontendParsedComputationOwnerBoundaryTests
  frontendParsedComputationOwnerEffectTests
  frontendParsedComputationRawOwnerRowTests
  frontendParsedComputationRawOwnerEffectTests
  frontendParsedComputationFunctionOwnerBoundaryTests
  frontendParsedComputationFunctionOwnerEffectTests
  frontendParsedComputationArgumentEffectTests
  frontendParsedFunctionCheckpointWorldTests
  frontendParsedExpectedLambdaHeaderTests
  frontendParsedExpectedComputationLambdaTests
  frontendParsedExpectedLambdaTypingTests
  frontendParsedExpectedLambdaLetBodyTests
  frontendParsedExpectedLambdaLetSpineTests
  adr0317ParsedExpectedLambdaArgumentTests
  adr0318LocalApplicationWithExpectedLambdaTests
  adr0319ParsedGroupedExpectedLambdaTests
  adr0320ParsedLocalApplicationWithGroupedExpectedLambdaTests
  adr0321ParsedTwoLevelGroupedExpectedLambdaTests
  adr0322ParsedLocalApplicationWithTwoLevelGroupedExpectedLambdaTests
  adr0323ParsedThreeOrMoreGroupedExpectedLambdaTests
  adr0324ParsedConditionalExpectedLambdaTests
  adr0325ParsedLocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaTests
  adr0326ParsedOneLevelGroupedConditionalExpectedLambdaTests
  adr0327ParsedLocalApplicationWithOneLevelGroupedConditionalExpectedLambdaTests
  adr0328ParsedTwoLevelGroupedConditionalExpectedLambdaTests
  adr0329ParsedLocalApplicationWithTwoLevelGroupedConditionalExpectedLambdaTests
  adr0330ParsedThreeLevelGroupedConditionalExpectedLambdaTests
  adr0331ParsedLocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaTests
  adr0332ParsedFourLevelGroupedConditionalExpectedLambdaTests
    *> adr0333ParsedLocalApplicationWithFourLevelGroupedConditionalExpectedLambdaTests
    *> adr0334ParsedFiveLevelGroupedConditionalExpectedLambdaTests
    *> adr0335ParsedLocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaTests
    *> adr0336ParsedSixLevelGroupedConditionalExpectedLambdaTests
    *> adr0337ParsedLocalApplicationWithSixLevelGroupedConditionalExpectedLambdaTests
    *> adr0338ParsedSevenLevelGroupedConditionalExpectedLambdaTests
    *> adr0339ParsedLocalApplicationWithSevenLevelGroupedConditionalExpectedLambdaTests
    *> genericGroupedConditionalTests
  frontendParsedRuntimeClosureValueTests
  frontendParsedSourceLambdaEffectTests
  frontendParsedSourceComputationBodyEffectTests
  frontendParsedClosedSourceClosureTests
  frontendParsedClosedSourceEvaluationTests
  frontendParsedClosedSourceConditionalTests
  frontendParsedClosedSourceDepthTests
  frontendParsedClosedSourceCoreImageTests
  frontendParsedClosedSourceDataBodyTests
  frontendParsedClosedSourceDataMatchTests
  frontendParsedExpectedDataLambdaApplicationTests
  frontendParsedExpectedDataLambdaInvocationTests
  frontendParsedExpectedDataLambdaBoundaryTests
  frontendParsedClosedSourceUnaryTests
  frontendParsedClosedSourceLogicalNotClosureTests
  frontendParsedClosedSourceBitNotClosureTests
  frontendParsedClosedSourceUnaryBoundaryTests
  frontendParsedExpectedBoolUnaryDataBridgeTests
  frontendParsedExpectedWordUnaryDataBridgeTests
  frontendParsedClosedSourceShortCircuitTests
  frontendParsedClosedSourceShortCircuitBoundaryTests
  frontendParsedExpectedBoolShortCircuitDataBridgeTests
  frontendParsedExpectedWordShortCircuitDataBridgeTests
  frontendParsedClosedStrictWordBinaryTests
  frontendParsedClosedStrictWordSavedCallsTests
  frontendParsedClosedStrictWordBinaryDataImageTests
  frontendParsedExpectedBoolStrictDataBridgeTests
  frontendParsedExpectedWordStrictDataBridgeTests
  frontendParsedDataDepthBridgeTests
  frontendParsedDataBodyDepthBridgeTests
  frontendParsedDirectDataLambdaDepthTests
  frontendParsedSavedDataLambdaDepthTests
  frontendParsedDataCalleeDepthTests
  frontendParsedBoundedCalleeDepthTests
  frontendParsedBoundedInputsDepthTests
  frontendParsedClosedSourceStoreReplayTests
  frontendParsedSelfApplicationTests
  frontendParsedClosedSourceOwnerTests
  frontendParsedOwnerCovarianceTests
  frontendParsedOwnerReflectionTests
  adr0314ParsedOwnerCoreConsumer
  adr0315ParsedOwnerExpectedDataLambdaApplicationTests
  adr0315ParsedOwnerExpectedDataLambdaInvocationTests
  adr0316ParsedCheckedDataOwnerTests
  testSyntaxIdentifier
  testSyntaxLexer
  testSyntaxParserBodyIsolation
  testSyntaxParserContracts
  testSyntaxParserDeclarationTrivia
  testSyntaxParserDiagnosticSuppression
  testSyntaxParserEnumTraitImpl
  testSyntaxParserLegacyRejection
  testSyntaxParserModules
  testSyntaxParserExports
  testSyntaxParserTypes
  testSyntaxParserYul
  testSyntaxParserYulChoiceRecovery
  testSyntaxParserRecovery
  testSyntaxParserReservedWords
  testSyntaxParserSignatures
  testSyntaxParserStatementFallback
  testSyntaxParserStatements
  Solcore.Test.SyntaxParserPublicStatementFuelTotalityProperties.run
  testSyntaxParserTerms
  testSyntaxParserTotality
  testSyntaxParserTrivia
  testSyntaxParserUpstreamDiagnosticPolicy
  testSyntaxParserUpstreamFixtures
  testSyntaxPublicBoundary
  testAbiKeccak256
  testAbiStaticWordMetadata
  testAbiStaticWordMetadataProperties
  testAbiStaticWordCodec
  testAbiStaticWordMethodTable
  testAbiStaticWordMethodTableProperties
  testAbiStaticWordDispatcher
  testAbiStaticWordContract
  AbiStaticWordEndToEnd.testAbiStaticWordEndToEnd
  testSemanticCore
  testPrimitiveAlgebra
  testM1cKernel
  testCoreArithmeticShift
  testCoreProducts
  testCoreFunctions
  testCoreHostMachine
  testCoreSums
  testCoreCells
  CoreRecursiveCells.run
  CoreLanguageResult.run
  SourceCoreLocalCell.run
  SourceCoreBasic.run
  SourceCoreControl.run
  SourceCorePrimitive.run
  SourceCoreLoops.run
  SourceCompilerLoops.run
  SourceCoreCalls.run
  SourceCoreRecursiveEntry.run
  SourceCoreFunctions.run
  SourceCoreFunctionEntry.run
  CoreLocalAssignment.run
  SourceCoreAssignments.run
  SourceCoreAssignmentFaultSites.run
  SourceCoreAssignmentEntries.run
  SourceCompilerAssignments.run
  SourceCompilerFunctions.run
  CoreWordMapping.run
  CoreIntegers.run
  CoreWireInteger.run
  CoreOrderedMapping.run
  SourceCoreIntegerEntry.run
  SourceCoreScalarExpressionReflection.run
  SourceCoreControlStatementMeaning.run
  SourceCoreDataCatalog.run
  SourceCoreDataEquality.run
  SourceCoreMappingWithDefault.run
  coreRuntimeUnificationTests
  SourceCoreNativeEntry.run
  SourceCoreRepresentationProjection.run
  SourceCompilerSourceBoundaryObservations.run
  SourceCoreGeneralEntry.run
  CoreIntegerAssignment.run
  SourceCoreIntegerAssignments.run
  SourceCoreIntegerFunctionEntry.run
  SourceCompilerIntegers.run
  SourceCoreDataExpressions.run
  SourceCoreDataMatches.run
  SourceCoreGroupedTuple.run
  SourceCoreGeneralFunctions.run
  SourceCoreDataValues.run
  SourceCoreLoopStatementReflection.run
  SourceCoreDataPlaces.run
  SourceCorePlanCatalog.run
  SourceCoreForHeaderCertificates.run
  SourceCoreForStatementReflection.run
  SourceCoreDataEqualityInitialization.run
  SourceCoreSession.run
  SourceCoreCompiler.run
  SourceCoreIndexedSession.run
  SourceCoreIndexedSessionFactories.run
  SourceCoreIndexedSessionInvocation.run
  SourceCoreRootDiscovery.run
  SourceCoreExecution.run
  SourceCoreShiftExecution.run
  SourceCoreUncheckedExecution.run
  SourceCoreClosedLambdaPublicExecution.run
  SourceCoreCapturedLambdaPublicExecution.run
  capturedClosureSessionTests
  SourceCoreDirectIssued.runForward
  SourceCoreInitialFunctionForward.run
  SourceCoreInitialLexicalFailure.runForward
  SourceCoreHeapSnapshot.run
  SourceCoreExecutionSnapshots.run
  SourceCoreActiveHeapPrefix.run
  SourceCompilerCoreGeneral.run
  SourceCompilerSession.run
  SourceCoreEvidence.run
  SourceCoreLocalPolymorphism.run
  SourceCoreLocalEvidence.run
  SourceCoreStageContracts.run
  SourceCoreStageCodebook.run
  SourceCoreCallableContracts.run
  SourceCoreStagedExecution.run
  CoreCallableContract.run
  SourceCoreCallableEquality.run
  SourceTypedClosureCaptureBoundary.run
  SourceCoreLocalPolymorphicExecution.run
  SourceCoreDataPlaceMappingProofs.run
  SourceCoreDataPlacePaths.run
  SourceCoreDataPlacePathFaults.run
  SourceCoreForLoopStatementCertificates.run
  SourceCoreLoopStatementMeaning.run
  SourceCoreLoopFiniteComposition.run
  CoreLocalLoop.run
  CoreTaggedFunction.run
  SourceCoreBasicEntry.run
  SourceCompilerCoreCells.run
  ContractLanguageResult.test
  testCoreBooleanConnectives
  testCoreBitwiseLogic
  testCoreByteSelection
  testCoreComparisonFlags
  testCoreConversions
  testCoreCountLeadingZeros
  testCoreDerivedComparisonFlags
  testCoreDerivedComparisons
  testCoreDerivedRenamingLaws
  testCoreDerivedSignedComparison
  testCoreDerivedSignedNonStrictComparisonFlags
  testCoreDerivedSignedNonStrictComparisons
  testCoreDirectWordComparisons
  testCoreLogicalShifts
  testCoreModularArithmetic
  testCoreModularExponentiation
  testCoreTernaryModularArithmetic
  testCoreNamedData
  testCoreRenaming
  testCoreRenamingRuntime
  testCoreSignExtension
  testCoreSignedComparison
  testCoreSignedComparisonFlags
  testCoreSignedDivision
  testCoreUnaryPrimitives
  testCoreUnsignedDivision
  testAddressBytesBE
  testAddressCodecCoherence
  testAddressWordBridge
  testAddressSelectedHostCode
  testAddressSelectedHostInputData
  testAddressSelectedHostInputDataParent
  testAddressSelectedHostInputDataSize
  testAddressSelectedHostInputDataSizeParent
  testAddressSelectedHostInputDataSizeStorage
  testAddressSelectedHostInputDataStorage
  testAddressSelectedHostInputWordBE
  testAddressSelectedHostInputWordBEParent
  testAddressSelectedHostInputWordBEStorage
  testAddressSelectedHostStorage
  testCurrentAddressExecution
  testCurrentAddressExecutionSession
  testCheckedCoreProgram
  testCheckedHostCoreWordProgramExecution
  testCheckedHostCoreWordCodeSelection
  testSelectedCheckedWordExecution
  testParentIndexedSelectedCheckedWordExecution
  testFrameContinuationContext
  testFrameContinuationContextTrapReasonMap
  testFrameResolutionResult
  testFrameResolutionResultContinuation
  testFrameResolutionResultTrapReasonMap
  testFrameTrace
  testFrameTraceExtension
  testFrameOutcome
  testFrameOutcomeTrapReasonMap
  testFrameEffectJournal
  testFrameCheckpointedWorkingPairStorageWrite
  testFrameCheckpointedWorkingPairWithStorageAddress
  testFrameCheckpointedWorkingPairWithPresentStorageAccount
  testFrameCheckpointedWorkingPairWithStorageAddressStorageRead
  testFrameCheckpointedWorkingPairWithPresentStorageAccountStorageRead
  testFrameCheckpointedWorkingPairWithPresentStorageAccountStorageWrite
  testFrameRunContinuation
  testFrameRunEffectComposition
  testFrameRunEffectContinuation
  testFrameRunEffectResolution
  testFrameRunEffectTrapPropagation
  testFrameRunResult
  testFrameRunResultTrapReasonMap
  testFrameStateResolution
  testParentIndexedFrameContinuationContext
  testParentIndexedFrameContinuationConstruction
  testParentIndexedSelectedExecutionResumption
  testParentIndexedSelectedExecutionFold
  testParentIndexedSelectedExecutionSession
  testParentIndexedFrameResolutionFold
  testParentIndexedFrameTrapRollback
  testParentIndexedFrameTrapPropagationPayload
  testHostDriverResumption
  testHostStorageDriverResumption
  testHostStorageInputData
  testTopLevelExecution
  testTopLevelObservation
  testContractCallWordBoundary
  testAdr0147BalancedTopLevelExecution
  Adr0147ValueCallBoundary.testAdr0147ValueCallBoundary
  Adr0148CreateContractWordBoundary.testAdr0148CreateContractWordBoundary
  testAdr0148CheckedAccountCreation
  testAdr0148CheckedCreationPreflight
  Adr0148CreationFailureBoundary.testAdr0148CreationFailureBoundary
  testAdr0148NestedCreationLifecycle
  testAdr0148CreationEndToEnd
  Adr0148CreationResumption.testAdr0148CreationResumption
  Adr0148CreationDepthOne.testAdr0148CreationDepthOne
  Adr0149EmitLogWordBoundary.testAdr0149EmitLogWordBoundary
  Adr0149TopLevelLogs.testAdr0149TopLevelLogs
  testAdr0149NestedLogExecution
  testAdr0149CreationLogExecution
  Adr0149BalancedTopLevelLogs.testAdr0149BalancedTopLevelLogs
  testTransactionJournal
  testTransactionHostStorageHandler
  testOneLevelNestedExecution
  testOneLevelNestedExecutionExtended
  testOneLevelNestedExecutionResumption
  Tests.ContractTupleEntryProfile.testContractTupleEntryProfile
  Tests.ContractBoundedBytesEntryProfile.testContractBoundedBytesEntryProfile
  Tests.ContractCallResume.testContractCallResume
  Tests.ContractCallChain.testContractCallChain
  Tests.ContractCallChoice.testContractCallChoice
  Tests.ContractEnumEntryProfile.testContractEnumEntryProfile
  testAdr0147NestedValueExecution
  testRuntimeScalars
  testWorldState
  testWorldStateBalance
  testWorldStateNonce
  AccountNonceIncrementProperties.testAccountNonceIncrement
  Adr0148ExecutionEnvironment.testAdr0148ExecutionEnvironment
  BalancedExecutionEnvironment.runBalancedExecutionEnvironmentTests
  ExecutionEnvironmentSeal.runExecutionEnvironmentSealTests
  testBalanceTransfer
  testWorldStateDeltaBalance
  testWorldStateDeltaCreation
  testWorldStateCode
  testWorldStateCodeWrite
  testWorldStateStorageRead
  testWorldStateStorageWriteAlgebra
  testWorldStateUpdateAlgebra
  testCoreWireCodec
  testCoreWireCodecFoundation
  testCoreWireConversions
  testCoreWireHost
  CoreWirePublic.testCoreWirePublic
  CoreSynthesisSeed.testCoreSynthesisSeed
  testCoreSynthesisFragment
  CoreSynthesisGenerator.testCoreSynthesisGenerator
  CoreSynthesisGeneratorV2.testCoreSynthesisGeneratorV2
  CoreSynthesisGeneratorV3.testCoreSynthesisGeneratorV3
  CoreSynthesisGeneratorV4.testCoreSynthesisGeneratorV4
  CoreSynthesisShrink.testCoreSynthesisShrink
  SourceSynthesisEmitter.testSourceSynthesisEmitter
  SourceSynthesisCases.testSourceSynthesisCases
  SourceInputEmitter.testSourceInputEmitter
  SourceInputCases.testSourceInputCases
  SourcePrimitiveEmitter.testSourcePrimitiveEmitter
  SourcePrimitiveCases.testSourcePrimitiveCases
  SourcePrimitiveCorpus.testSourcePrimitiveCorpus
  SourceAssemblyCases.testSourceAssemblyCases
  SourceAssemblyMemoryCases.testSourceAssemblyMemoryCases
  SourceEnumCases.testSourceEnumCases
  SourceTraitCases.testSourceTraitCases
  SourceHierarchyCases.testSourceHierarchyCases
  SourceMemoryValuesCases.testSourceMemoryValuesCases
  SourceMemoryCallsCases.testSourceMemoryCallsCases
  SourceRevertDataCases.testSourceRevertDataCases
  SourceRevertDataCases.testSourceHaltCases
  SourceIntegerCases.testSourceIntegerCases
  SourceArrayCases.testSourceArrayCases
  CallGraphGenerator.testCallGraphGenerator
  SourceCallGraphEmitter.testSourceCallGraphEmitter
  SourceCallGraphCases.testSourceCallGraphCases
  SourceCallGraphCorpus.testSourceCallGraphCorpus
  SourceCallGraphLoopEmitter.testSourceCallGraphLoopEmitter
  SourceCallGraphLoopCases.testSourceCallGraphLoopCases
  SourceCallGraphLoopCorpus.testSourceCallGraphLoopCorpus
  SourceAssemblyLoopCases.testSourceAssemblyLoopCases
  SourceAggregateCallGraphEmitter.testSourceAggregateCallGraphEmitter
  SourceAggregateCallGraphCases.testSourceAggregateCallGraphCases
  SourceAggregateCallGraphCorpus.testSourceAggregateCallGraphCorpus
  SourceFunctionEmitter.testSourceFunctionEmitter
  SourceFunctionCases.testSourceFunctionCases
  SourceMutationEmitter.testSourceMutationEmitter
  SourceMutationCases.testSourceMutationCases
  SourceAggregateEmitter.testSourceAggregateEmitter
  SourceAggregateCases.testSourceAggregateCases
  SourceLoopEmitter.testSourceLoopEmitter
  SourceLoopCases.testSourceLoopCases
  SourceGenericEmitter.testSourceGenericEmitter
  SourceGenericCases.testSourceGenericCases
  SourceClosureEmitter.testSourceClosureEmitter
  SourceClosureCases.testSourceClosureCases
  SourceComptimeEmitter.testSourceComptimeEmitter
  SourceComptimeCases.testSourceComptimeCases
  SourceModuleEmitter.testSourceModuleEmitter
  SourceModuleCases.testSourceModuleCases
  SourceGeneratorRevisionCases.testSourceGeneratorRevisionCases
  SourceStatefulGeneratorRevisionCases.testSourceStatefulGeneratorRevisionCases
  SourceStatefulSequenceCases.testSourceStatefulSequenceCases
  SourceSeededInputCases.testSourceSeededInputCases
  SourceSwarmMaskCases.testSourceSwarmMaskCases
  SourceEmitterSupportCases.testSourceEmitterSupportCases
  SourceRevisionFourCases.testSourceRevisionFourCases
  SourceAcceptanceCases.testSourceAcceptanceCases
  SourceNestedLoopCases.testSourceNestedLoopCases
  SourceRecursionCases.testSourceRecursionCases
  SourceRecursiveLoopCases.testSourceRecursiveLoopCases
  SourceLoopClosureCases.testSourceLoopClosureCases
  SourceStorageEmitter.testSourceStorageEmitter
  SourceStorageCases.testSourceStorageCases
  SourceStorageRollbackEmitter.testSourceStorageRollbackEmitter
  SourceStorageRollbackCases.testSourceStorageRollbackCases
  SourceNestedCallEmitter.testSourceNestedCallEmitter
  SourceNestedCallCases.testSourceNestedCallCases
  testDetailedCoreChecker
  testWorkspacePathIdentity
  testWorkspaceCanonicalValidation
  testWorkspaceEqualContentIdentity
  testWorkspaceValidationErrors
  testWorkspaceValidationEquivalence

end Tests

def main : IO UInt32 := do
  Tests.SourcePathExtensions.run
  Tests.RustYulPrimitives.run
  Tests.RustHullDecode.run
  Tests.RustHullMemory.run
  Tests.RustHullKeccak.run
  Tests.RustHullYul.run
  Tests.RustHullAmbient.run
  Tests.RustHullCreation.run
  Tests.RustHullAccountLifecycle.run
  Tests.RustHullAccountState.run
  Tests.RustHullAccountInspection.run
  Tests.RustHullCreationRuntime.run
  Tests.RustHullWorld.run
  Tests.RustHullCreationAccounts.run
  Tests.RustHullMemorySnapshot.run
  Tests.RustHullImageComparison.run
  Tests.RustHullWorldEffects.run
  Tests.RustHullLowering.run
  Tests.RustHullCodeImage.run
  Tests.RustHullObjectLinking.run
  Tests.RustHullLinkedContract.run
  Tests.RustHullHashes.run
  Tests.RustHullSecp256k1.run
  Tests.RustHullPrecompiles.run
  Tests.RustHullP256.run
  Tests.RustHullLogs.run
  Tests.RustHullCalls.run
  Tests.RustHullEffectReceipts.run
  Tests.RustHullAccounts.run
  Tests.RustHullScalarExecution.run
  Tests.RustHullPureCorrespondence.run
  Tests.RustHullRankedCorrespondence.run
  Tests.RustHullRecursiveCorrespondence.run
  Tests.RustHullLocalCallsCorrespondence.run
  Tests.RustHullLoopCorrespondence.run
  Tests.RustHullFaultCorrespondence.run
  Tests.RustHullProductCorrespondence.run
  Tests.RustHullMatchCorrespondence.run
  Tests.RustHullMemoryCorrespondence.run
  Tests.RustHullRuntimeEffectsCorrespondence.run
  Tests.RustHullEnvironmentCorrespondence.run
  Tests.RustHullLogCorrespondence.run
  Tests.RustHullTerminationCorrespondence.run
  Tests.RustHullMemoryCopyCorrespondence.run
  Tests.RustHullKeccakCorrespondence.run
  Tests.RustHullAccountCorrespondence.run
  Tests.RustHullCodeImageCorrespondence.run
  Tests.RustHullReturnDataCorrespondence.run
  Tests.RustHullCallCorrespondence.run
  Tests.RustHullChildCallCorrespondence.run
  Tests.RustHullNestedChildCallRuntime.run
  Tests.RustHullCallModeRuntime.run
  Tests.RustHullLifecycleRuntime.run
  Tests.RustHullRootCallRuntime.run
  Tests.SourceCoreSelectedLexicalFailure.run
  Tests.SourceCoreSelectedOrdinaryStageLift.run
  Tests.SourceCoreSelectedLexicalSourceFirst.run
  Tests.SourceCoreSelectedNamedBuiltinDirect.run
  Tests.SourceCoreSelectedBoxOutput.run
  Tests.SourceCoreSelectedCompositeProfile.run
  Tests.SourceCoreSelectedPrimitiveProfile.run
  Tests.SourceCoreSelectedBodyControl.run
  Tests.SourceCoreSelectedCoercedDirect.run
  Tests.SourceCoreSelectedLoop.run
  Tests.SourceCoreSelectedMatch.run
  Tests.SourceCoreSelectedCompletion.run
  Tests.SourceCoreSelectedCompound.run
  Tests.SourceCoreSelectedBitNot.run
  Tests.SourceCoreSelectedProjectedAssignment.run
  Tests.SourceCoreSelectedProjectedBitNot.run
  Tests.SourceCoreSelectedProxy.run
  Tests.SourceCoreSelectedGeneralKey.run
  Tests.SourceCoreSelectedGeneralizedLocal.typingProbe
  Tests.SourceCoreSelectedGeneralizedLocal.run
  Tests.SourceCoreSelectedGeneralizedLocal.ObservedRuntime.run
  Tests.SourceCoreSelectedInterleavedLocal.FailureBridge.publicProbe
  Tests.SourceCoreSelectedFaultingLocal.FailureBridge.publicProbe
  Tests.SourceCoreSelectedInterleavedLocal.typingProbe
  Tests.SourceCoreSelectedInterleavedLocal.publicProbe
  Tests.SourceCoreSelectedInterleavedLocal.probe
  Tests.SourceCoreSelectedCapturedDirect.run
  Tests.SourceCoreCompilationScope.run
  Tests.SourceCoreSelectedOperatorAlias.run
  Tests.SourceCoreSelectedCompilationProfile.run
  Tests.SourceCoreMethodOriginEvidence.SelectedSourceOutcomes.run
  Tests.SourceCoreGeneralizedExport.probe
  Tests.SourceCoreGeneralizedExport.SourcePublicRuntime.run
  Tests.SourceCoreMixedImperative.typingProbe
  Tests.SourceCoreMixedImperative.probe
  Tests.SourceCoreMixedImperative.ObservedRuntime.run
  Tests.SourceCoreMixedWhile.typingProbe
  Tests.SourceCoreMixedWhile.probe
  Tests.SourceCoreMixedWhile.ObservedRuntime.run
  Tests.SourceCoreMixedBuiltinValue.typingProbe
  Tests.SourceCoreMixedBuiltinValue.probe
  Tests.SourceCoreMixedBuiltinValue.ObservedRuntime.run
  Tests.SourceCoreMixedBuiltinValue.HandleRuntime.run
  Tests.SourceCoreMixedFor.typingProbe
  Tests.SourceCoreMixedFor.probe
  Tests.SourceCoreMixedFor.ObservedRuntime.run
  Tests.SourceCoreMixedConditional.typingProbe
  Tests.SourceCoreMixedConditional.probe
  Tests.SourceCoreMixedConditional.ObservedRuntime.run
  Tests.SourceCoreMixedProjected.typingProbe
  Tests.SourceCoreMixedProjected.probe
  Tests.SourceCoreMixedProjected.ObservedRuntime.run
  Tests.SourceCoreMixedOperators.typingProbe
  Tests.SourceCoreMixedOperators.probe
  Tests.SourceCoreMixedOperators.ObservedRuntime.run
  Tests.SourceCoreMixedIndexRead.typingProbe
  Tests.SourceCoreMixedIndexRead.probe
  Tests.SourceCoreMixedIndexRead.ObservedRuntime.run
  Tests.SourceCoreGeneralizedBodyExpression.typingProbe
  Tests.SourceCoreGeneralizedBodyExpression.nativeProbe
  Tests.SourceCoreGeneralizedBodyExpression.ObservedRuntime.run
  Tests.SourceCoreGeneralizedLexicalBody.typingProbe
  Tests.SourceCoreGeneralizedLexicalBody.nativeProbe
  Tests.SourceCoreGeneralizedLexicalBody.ObservedRuntime.run
  Tests.SourceCoreGeneralizedExport.SourcePublicSelectedRuntime.run
  Tests.SourceCoreGeneralizedExport.SourcePublicNamedSelectedRuntime.run
  Tests.SourceCoreSelectedFaultingLocal.FailureBridge.selectedRuntime
  Tests.staticSemanticsSpineTests
  Tests.run
  Tests.SourceScalarMeaning.testSourceScalarMeaning
  Tests.RustHullPrecompileCorrespondence.run
  Tests.SourceKeyedStorageEmitter.testSourceKeyedStorageEmitter
  Tests.SourceKeyedStorageCases.testSourceKeyedStorageCases
  Tests.SourceKeyedStorageCorpus.testSourceKeyedStorageCorpus
  Tests.SourceDynamicArrayEmitter.testSourceDynamicArrayEmitter
  Tests.SourceDynamicArrayCases.testSourceDynamicArrayCases
  Tests.SourceDynamicArrayCorpus.testSourceDynamicArrayCorpus
  Tests.SourceMalformedCalldataGolden.testSourceMalformedCalldataGolden
  Tests.SourceMalformedCalldataCases.testSourceMalformedCalldataCases
  Tests.SourceMalformedCalldataCorpus.testSourceMalformedCalldataCorpus
  Tests.SourceMalformedNestedArrayGolden.testSourceMalformedNestedArrayGolden
  Tests.SourceMalformedNestedArrayCases.testSourceMalformedNestedArrayCases
  Tests.SourceMalformedNestedArrayCorpus.testSourceMalformedNestedArrayCorpus
  Tests.SourceMalformedBytesGolden.testSourceMalformedBytesGolden
  Tests.SourceMalformedBytesCases.testSourceMalformedBytesCases
  Tests.SourceMalformedBytesCorpus.testSourceMalformedBytesCorpus
  Tests.SourceMethodsGolden.testSourceMethodsGolden
  Tests.SourceMethodsCases.testSourceMethodsCases
  Tests.SourceMethodsCorpus.testSourceMethodsCorpus
  Tests.SourceStorageLoopGolden.testSourceStorageLoopGolden
  Tests.SourceStorageLoopCases.testSourceStorageLoopCases
  Tests.SourceStorageLoopCorpus.testSourceStorageLoopCorpus
  Tests.SourceKeccakLoopGolden.testSourceKeccakLoopGolden
  Tests.SourceKeccakLoopCases.testSourceKeccakLoopCases
  Tests.SourceKeccakLoopCorpus.testSourceKeccakLoopCorpus
  Tests.SourceAssemblyStorageLoopGolden.testSourceAssemblyStorageLoopGolden
  Tests.SourceAssemblyStorageLoopCases.testSourceAssemblyStorageLoopCases
  Tests.SourceAssemblyStorageLoopCorpus.testSourceAssemblyStorageLoopCorpus
  Tests.SourceAssemblyKeccakLoopGolden.testSourceAssemblyKeccakLoopGolden
  Tests.SourceAssemblyKeccakLoopCases.testSourceAssemblyKeccakLoopCases
  Tests.SourceAssemblyKeccakLoopCorpus.testSourceAssemblyKeccakLoopCorpus
  Tests.SourceAdtStorageGolden.testSourceAdtStorageGolden
  Tests.SourceAdtStorageCases.testSourceAdtStorageCases
  Tests.SourceAdtStorageCorpus.testSourceAdtStorageCorpus
  Tests.SourceTupleReturnGolden.testSourceTupleReturnGolden
  Tests.SourceTupleReturnCases.testSourceTupleReturnCases
  Tests.SourceTupleReturnCorpus.testSourceTupleReturnCorpus
  Tests.SourceBytesReturnGolden.testSourceBytesReturnGolden
  Tests.SourceBytesReturnCases.testSourceBytesReturnCases
  Tests.SourceBytesReturnCorpus.testSourceBytesReturnCorpus
  Tests.SourceEnumReturnGolden.testSourceEnumReturnGolden
  Tests.SourceEnumReturnCases.testSourceEnumReturnCases
  Tests.SourceEnumReturnCorpus.testSourceEnumReturnCorpus
  Tests.SourceEnumArgumentGolden.testSourceEnumArgumentGolden
  Tests.SourceEnumArgumentCases.testSourceEnumArgumentCases
  Tests.SourceEnumArgumentCorpus.testSourceEnumArgumentCorpus
  Tests.SourceEnumArrayGolden.testSourceEnumArrayGolden
  Tests.SourceEnumArrayCases.testSourceEnumArrayCases
  Tests.SourceEnumArrayCorpus.testSourceEnumArrayCorpus
  Tests.SourceArrayReturnGolden.testSourceArrayReturnGolden
  Tests.SourceArrayReturnCases.testSourceArrayReturnCases
  Tests.SourceArrayReturnCorpus.testSourceArrayReturnCorpus
  Tests.SourceConstructorArgumentGolden.testSourceConstructorArgumentGolden
  Tests.SourceCallReturnGolden.testSourceCallReturnGolden
  Tests.SourceCallSequenceGolden.testSourceCallSequenceGolden
  Tests.SourceCallReturnCases.testSourceCallReturnCases
  Tests.SourceCallSequenceCases.testSourceCallSequenceCases
  Tests.SourceCallReturnCorpus.testSourceCallReturnCorpus
  Tests.SourceCallSequenceCorpus.testSourceCallSequenceCorpus
  Tests.SourceCallBranchGolden.testSourceCallBranchGolden
  Tests.SourceCallBranchCases.testSourceCallBranchCases
  Tests.SourceCallBranchCorpus.testSourceCallBranchCorpus
  Tests.SourceConstructorArgumentCases.testSourceConstructorArgumentCases
  Tests.SourceConstructorArgumentCorpus.testSourceConstructorArgumentCorpus
  Tests.SourceAggregatePrimitives.testSourceAggregatePrimitives
  Tests.SourceAggregateMeaning.testSourceAggregateMeaning
  Tests.SourceEventLogEmitter.testSourceEventLogEmitter
  Tests.SourceEventLogCases.testSourceEventLogCases
  Tests.SourceEventLogCorpus.testSourceEventLogCorpus
  Tests.RustHullCreationCorrespondence.run
  Tests.SourceAggregateCallGraphMeaning.testSourceAggregateCallGraphMeaning
  Tests.SourceCallValueEmitter.testSourceCallValueEmitter
  Tests.SourceCallValueCases.testSourceCallValueCases
  Tests.SourceCallValueCorpus.testSourceCallValueCorpus
  Tests.RustHullCreationAdmittedCorrespondence.run
  Tests.SourceCallGraphLoopMeaning.testSourceCallGraphLoopMeaning
  Tests.SourceDynamicBytesEmitter.testSourceDynamicBytesEmitter
  Tests.SourceDynamicBytesCases.testSourceDynamicBytesCases
  Tests.SourceDynamicBytesCorpus.testSourceDynamicBytesCorpus
  Tests.RustHullCreationFaultCorrespondence.run
  Tests.SourceCoreGeneralizedExport.AcceptedTickRuntime.run
  Tests.SourceLoopMeaning.testSourceLoopMeaning
  Tests.SourceForwardedCallEmitter.testSourceForwardedCallEmitter
  Tests.SourceForwardedCallCases.testSourceForwardedCallCases
  Tests.SourceForwardedCallCorpus.testSourceForwardedCallCorpus
  Tests.RustHullRevertCorrespondence.run
  Tests.SourceGenericMeaning.testSourceGenericMeaning
  Tests.SourceStorageMappingEmitter.testSourceStorageMappingEmitter
  Tests.SourceStorageMappingCases.testSourceStorageMappingCases
  Tests.SourceStorageMappingCorpus.testSourceStorageMappingCorpus
  Tests.RustHullAssemblyCorrespondence.run
  Tests.SourceStorageMeaning.testSourceStorageMeaning
  Tests.RustHullYulBlockCorrespondence.run
  Tests.SourceStorageLedgerEmitter.testSourceStorageLedgerEmitter
  Tests.SourceStorageLedgerCases.testSourceStorageLedgerCases
  Tests.SourceStorageLedgerCorpus.testSourceStorageLedgerCorpus
  Tests.SourceRollbackMeaning.testSourceRollbackMeaning
  Tests.RustHullYulControlCorrespondence.run
  Tests.SourceLongBytesEmitter.testSourceLongBytesEmitter
  Tests.SourceLongBytesCases.testSourceLongBytesCases
  Tests.SourceLongBytesCorpus.testSourceLongBytesCorpus
  Tests.SourceKeyedMeaning.testSourceKeyedMeaning
  Tests.SourceLogMeaning.testSourceLogMeaning
  Tests.RustHullYulArithmeticCorrespondence.run
  Tests.SourceNestedArrayEmitter.testSourceNestedArrayEmitter
  Tests.SourceNestedArrayCases.testSourceNestedArrayCases
  Tests.SourceNestedArrayCorpus.testSourceNestedArrayCorpus
  IO.println "solcore-lean tests passed"
  return 0
