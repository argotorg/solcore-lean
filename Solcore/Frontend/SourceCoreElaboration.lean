import Solcore.Frontend.ProgramChecking
import Solcore.Frontend.SourceSpecialization
import Solcore.Frontend.SourceStagedValue
import Solcore.Frontend.WordLiteral
import Solcore.Core.Primitive
import Solcore.Resolved.Typing

/-!
The first executable bridge from occurrence-addressed typed source to Semantic
Core.  This deliberately small profile accepts only the closed builtin local
fragment already represented by `Resolved.Expr`; every staged source feature
fails with a located elaboration error instead of being assigned an invented
runtime meaning.
-/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreElaboration

open SourceInference TypeSystem

/-- A failure is attached either to the declaration boundary, a typed source
occurrence, or an input binder whose type could not be specialized. -/
inductive ErrorSite where
  | declaration (id : Resolved.DeclarationId)
  | occurrence (id : OccurrenceId)
  | binder (id : Resolved.LocalId)
  deriving Repr, DecidableEq

/-- Typed expression forms intentionally left outside the first Core bridge. -/
inductive UnsupportedExpression where
  | declarationReference
  | call
  | lambda
  | constructor
  | member
  | proxy
  | index
  deriving Repr, BEq, DecidableEq

/-- Statement forms outside the tail-normal executable profile. -/
inductive UnsupportedStatement where
  | expression
  | assignment
  | loop
  | loopControl
  deriving Repr, BEq, DecidableEq

/-- Statements whose control-flow meaning cannot be preserved before the end
of the current statement list. -/
inductive NonTailStatement where
  | returnStmt
  | ifThen
  | block
  | matchWith
  deriving Repr, BEq, DecidableEq

/-- Identify the branch of a tail conditional that can fall through. -/
inductive ConditionalBranch where
  | thenBranch
  | elseBranch
  deriving Repr, BEq, DecidableEq

/-- Precise rejection reasons at the typed-source-to-Core boundary. -/
inductive ErrorReason where
  | ownerMismatch
      (expected actual : Resolved.DeclarationId)
  | missingNode
  | expectedExpressionNode
  | expectedStatementNode
  | coercionsPresent (coercions : List CoercionStep)
  | requirementsPresent (requirements : List RequirementId)
  | flexibleTypeVariable (id : TypeVarId)
  | rigidTypeParameter (id : TypeParameterId)
  | nominalType (id : Resolved.DeclarationId)
  | unsupportedType (type : Ty)
  | polymorphicInput (variables : List TypeVarId)
  | duplicateInput (id : Resolved.LocalId)
  | polymorphicLocal (variables : List TypeVarId)
  | duplicateLocal (id : Resolved.LocalId)
  | unsupportedExpression (kind : UnsupportedExpression)
  | unsupportedStatement (kind : UnsupportedStatement)
  | uninitializedLet
  | nonTailStatement (kind : NonTailStatement)
  | missingElseBranch
  | statementListFallthrough
  | blockFallthrough
  | conditionalBranchFallthrough (branch : ConditionalBranch)
  | invalidWordLiteral (literal : Syntax.CoreLiteralValue)
  | integerLiteralTargetTypeMismatch (target node : Ty)
  | integerLiteralRequirementsMismatch
      (expected actual : List RequirementId)
  | invalidIntegerLiteralSource (literal : Syntax.CoreLiteralValue)
  | integerLiteralRawValueMismatch (decoded recorded : Nat)
  | missingIntegerLiteralRequirement (requirement : RequirementId)
  | duplicateIntegerLiteralRequirements
      (requirement : RequirementId) (count : Nat)
  | integerLiteralPredicateMismatch
      (requirement : RequirementId)
      (expected actual : ProgramPredicate)
  | integerLiteralEvidenceGoalMismatch
      (requirement : RequirementId)
      (expected actual : ProgramPredicate)
  | unresolvedIntegerLiteralEvidence (requirement : RequirementId)
  | integerLiteralImplementationMismatch
      (requirement : RequirementId)
      (expected actual : ProgramImplId)
  | integerLiteralPremiseCountMismatch
      (requirement : RequirementId) (expected actual : Nat)
  | builtinFunctionCalleeNotReference (function : BuiltinFunctionId)
  | builtinFunctionCalleeIdentityMismatch
      (expected actual : BuiltinFunctionId)
  | builtinFunctionCalleeSpellingMismatch
      (function : BuiltinFunctionId) (expected actual : String)
  | builtinFunctionCalleeTypeMismatch
      (function : BuiltinFunctionId) (expected actual : Ty)
  | builtinFunctionCallTypeMismatch
      (function : BuiltinFunctionId) (expected actual : Ty)
  | builtinFunctionArgumentArityMismatch
      (function : BuiltinFunctionId) (expected actual : Nat)
  | builtinFunctionArgumentTypeMismatch
      (function : BuiltinFunctionId) (index : Nat) (expected actual : Ty)
  | builtinFunctionRequirementsPresent
      (function : BuiltinFunctionId) (requirements : List RequirementId)
  | builtinFunctionCoercionsPresent
      (function : BuiltinFunctionId) (coercions : List CoercionStep)
  | builtinBooleanSpellingMismatch
      (value : Bool) (expected actual : String)
  | stagedIntegerTypeMismatch (expected actual : Ty)
  | stagedIntegerLocalSpellingMismatch
      (binder : Resolved.LocalId) (expected actual : String)
  | stagedIntegerCallRequirementsMismatch
      (expected actual : List RequirementId)
  | stagedIntegerCallArgumentArityMismatch (expected actual : Nat)
  | stagedIntegerFunctionTypeMismatch (expected actual : Ty)
  | stagedIntegerArgumentArityMismatch (expected actual : Nat)
  | stagedIntegerStatementNotClosed
  | stagedIntegerExpressionNotClosed
  | stagedIntegerDepthLimit
  | stagedWordTypeMismatch (expected actual : Ty)
  | stagedWordExpressionNotClosed
  | stagedWordDepthLimit
  | stagedBoolTypeMismatch (expected actual : Ty)
  | stagedBoolExpressionNotClosed
  | stagedBoolDepthLimit
  | stagedValueExpressionStageMissing
  | stagedValueExpressionRuntime
  | stagedValueExpressionDeferred
  | stagedValueBinderStageMissing
  | stagedValueBinderRuntime
  | stagedValueBinderDeferred
  | stagedValueTypeMismatch (expected actual : Ty)
  | stagedValueLocalSpellingMismatch
      (binder : Resolved.LocalId) (expected actual : String)
  | stagedValueInvalidUnaryOperand
      (operator : Syntax.UnaryOp) (actual : Ty)
  | stagedValueInvalidBinaryOperands
      (operator : Syntax.BinaryOp) (left right : Ty)
  | stagedValueUnaryRequirementsMismatch
      (expected actual : List RequirementId)
  | stagedValueUnaryOperandTypeMismatch
      (expected actual : Core.Ty)
  | stagedValueUnaryResultTypeMismatch
      (expected actual : Core.Ty)
  | stagedValueBinaryRequirementsMismatch
      (expected actual : List RequirementId)
  | stagedValueBinaryLeftTypeMismatch
      (expected actual : Core.Ty)
  | stagedValueBinaryRightTypeMismatch
      (expected actual : Core.Ty)
  | stagedValueBinaryResultTypeMismatch
      (expected actual : Core.Ty)
  | stagedValueCallRequirementsMismatch
      (expected actual : List RequirementId)
  | stagedValueCallArgumentArityMismatch (expected actual : Nat)
  | stagedValueCallResultTypeMismatch (expected actual : Ty)
  | stagedValueArgumentArityMismatch (expected actual : Nat)
  | stagedValueFunctionTypeMismatch (expected actual : Ty)
  | stagedValueSpecializationKeyMismatch
      (expected actual : Resolved.DeclarationId)
  | stagedValueSpecializationArgumentsMismatch
      (expected actual : List Ty)
  | stagedValueAnalysisFailure (error : SourceStageAnalysis.Error)
  | stagedValueAnalysisMismatch
      (expected actual : SourceStageAnalysis.Analysis)
  | stagedValueRequirementsMismatch
      (expected actual : List RequirementId)
  | stagedValueStatementNotClosed
  | stagedValueDepthLimit
  | matchHiddenOwnerMismatch
      (expected actual : Resolved.DeclarationId)
  | duplicateMatchHidden (id : Resolved.LocalId)
  | matchPatternTypeMismatch (expected actual : Ty)
  | matchPatternSourceMismatch
  | matchPatternRequirementsMismatch
      (expected actual : List RequirementId)
  | matchRequirementsMismatch
      (expected actual : List RequirementId)
  | matchWithoutFallback
  | unknownLocal (id : Resolved.LocalId)
  | expressionDepthLimit
  | statementDepthLimit
  | typedNodeTypeMismatch (expected actual : Core.Ty)
  | resolvedLoweringFailed
  | coreInferenceFailed
  | returnTypeMismatch (expected actual : Core.Ty)
  | callRequirementsMismatch
      (expected actual : List RequirementId)
  | callArgumentArityMismatch (expected actual : Nat)
  | unaryRequirementsMismatch
      (expected actual : List RequirementId)
  | binaryRequirementsMismatch
      (expected actual : List RequirementId)
  | identityCoercionStep
      (index : Nat) (requirement : RequirementId) (type : Ty)
  | coercionPathDiscontinuity
      (index : Nat) (expectedSource actualSource : Ty)
  | coercionPathTargetMismatch (expectedTarget actualTarget : Ty)
  | missingCoercionRequirement
      (requirement : RequirementId) (attached : List RequirementId)
  | duplicateCoercionRequirement (requirement : RequirementId)
  | coercionPlanSourceTypeMismatch
      (requirement : RequirementId) (expected actual : Core.Ty)
  | coercionPlanTargetTypeMismatch
      (requirement : RequirementId) (expected actual : Core.Ty)
  | coercionPlanRequirementsMismatch
      (requirement : RequirementId)
      (expected actual : List RequirementId)
  | unknownConsumedRequirement (requirement : RequirementId)
  | duplicateConsumedRequirement (requirement : RequirementId)
  | unconsumedRequirements (requirements : List RequirementId)
  deriving Repr, DecidableEq

structure Error where
  site : ErrorSite
  reason : ErrorReason
  deriving Repr, DecidableEq

/-- A checked source function lowered to an open Semantic Core expression.
`inputs` fixes both stable resolved identities and the positional Core context. -/
structure ElaboratedFunction where
  declaration : Resolved.DeclarationId
  inputs : Resolved.Context
  resolved : Resolved.Expr
  core : Core.Expr
  returnType : Core.Ty
  resolvedLowered : resolved.lower? inputs.ids = some core
  coreTypeChecked : Core.infer? inputs.values core = some returnType
  deriving Repr

/-- The source-local half of elaboration, before stable identities are lowered
to Core positions and the resulting Core term is independently rechecked.
`unconsumedRequirements` is retained at this boundary so call-aware consumers
cannot accidentally bypass the existing evidence-execution gate. -/
structure BodyDraft where
  declaration : Resolved.DeclarationId
  inputs : Resolved.Context
  resolved : Resolved.Expr
  returnType : Core.Ty
  rootOccurrence : OccurrenceId
  unconsumedRequirements : List RequirementId
  deriving Repr

/-- One recursively lowered expression together with the function-local
requirements discharged inside it.  The list is kept explicit so the enclosing
function can reconcile every discharge against its canonical
`SolvedRequirement` table before Core lowering. -/
structure LoweredExpression where
  resolved : Resolved.Expr
  consumedRequirements : List RequirementId
  deriving Repr, DecidableEq

/-- A call policy first declares the exact argument types and requirements it
owns, then receives already checked and recursively lowered arguments in source
order.  Keeping argument traversal in this module prevents a policy from
claiming requirements belonging to an argument it did not actually lower. -/
structure CallPlan (error : Type) where
  argumentTypes : List Core.Ty
  consumedRequirements : List RequirementId
  build : List Resolved.Expr → Except error Resolved.Expr

/-- A call-aware consumer plans an otherwise staged call.  The error type is
parametric so whole-program linkers can retain their own exact failures while
lifting ordinary source-to-Core failures through `lowerFunctionBodyWith`. -/
abbrev CallElaborator (error : Type) :=
  Resolved.Context → ExpressionNode → ExpressionId →
  List ExpressionId → CallResolution → Except error (CallPlan error)

/-- A late-bound query for a Core-representable argument value known in the
caller's current lexical staged environment.  `none` means that ordinary Core
lowering remains authoritative for that occurrence. -/
abbrev StagedValueArgumentOracle (error : Type) :=
  ExpressionId → Except error (Option SourceStagedValue.Value)

/-- Internal runtime-call planning hook used by whole-program specialization.
The extra oracle does not transfer requirement ownership: arguments are still
lowered exactly once by Source Core after the plan has been checked. -/
abbrev StagedAwareCallElaborator (error : Type) :=
  StagedValueArgumentOracle error → CallElaborator error

/-- Positional staged knowledge for one call-site-specific runtime draft.
Unknown and runtime inputs remain `none`; a known marked input carries its
validated Core-representable value. -/
abbrev KnownStagedValueInputs :=
  List (Option SourceStagedValue.Value)

/-- A staged-integer call policy declares its exact source argument types and
function-local call requirements before receiving the already validated and
evaluated signed arguments in source order.  The result deliberately contains
no requirement IDs: obligations consumed in the callee belong to the callee's
ledger and must be reconciled at that function boundary. -/
structure StagedIntegerCallPlan (error : Type) where
  argumentTypes : List Ty
  consumedRequirements : List RequirementId
  invoke : List Int → Except error Int

/-- A whole-program consumer may execute an otherwise non-closed direct source
call while the staged evaluator retains argument lookup, type checking,
left-to-right evaluation, and caller-local requirement accounting. -/
abbrev StagedIntegerCallElaborator (error : Type) :=
  ExpressionNode → ExpressionId → List ExpressionId →
  DeclarationInstantiation → Except error (StagedIntegerCallPlan error)

/-- A general staged call policy fixes source argument/result types and the
caller-local requirements it consumes before receiving already evaluated
Core-representable values in source order. -/
structure StagedValueCallPlan (error : Type) where
  argumentTypes : List Ty
  resultType : Ty
  consumedRequirements : List RequirementId
  invoke : List SourceStagedValue.Value →
    Except error SourceStagedValue.Value

/-- Whole-program hook for direct calls in the bounded staged-value domain. -/
abbrev StagedValueCallElaborator (error : Type) :=
  ExpressionNode → ExpressionId → List ExpressionId →
  DeclarationInstantiation → Except error (StagedValueCallPlan error)

/-- One executable coercion step in the staged-value domain.  The Core
endpoints and exact requirement row are declared before the policy receives a
value, keeping typed-path validation and caller-local accounting in Source
Core. -/
structure StagedValueCoercionPlan (error : Type) where
  sourceType : Core.Ty
  targetType : Core.Ty
  consumedRequirements : List RequirementId
  invoke : SourceStagedValue.Value →
    Except error SourceStagedValue.Value

/-- Whole-program hook for evidence-bearing coercions encountered while
evaluating a Core-representable staged expression. -/
abbrev StagedValueCoercionElaborator (error : Type) :=
  ExpressionNode → CoercionStep →
  Except error (StagedValueCoercionPlan error)

/-- A requirement-bearing staged unary operation fixes both Core endpoints and
the exact caller-local requirements it consumes before receiving its already
evaluated operand. -/
structure StagedValueRequiredUnaryPlan (error : Type) where
  operandType : Core.Ty
  resultType : Core.Ty
  consumedRequirements : List RequirementId
  invoke : SourceStagedValue.Value →
    Except error SourceStagedValue.Value

/-- Whole-program hook for an evidence-selected unary implementation method. -/
abbrev StagedValueRequiredUnaryElaborator (error : Type) :=
  ExpressionNode → Syntax.UnaryOp → ExpressionId →
  Except error (StagedValueRequiredUnaryPlan error)

/-- A requirement-bearing staged binary operation fixes both operand Core
types, its result type, and its exact caller-local requirement discharge. -/
structure StagedValueRequiredBinaryPlan (error : Type) where
  leftType : Core.Ty
  rightType : Core.Ty
  resultType : Core.Ty
  consumedRequirements : List RequirementId
  invoke : SourceStagedValue.Value → SourceStagedValue.Value →
    Except error SourceStagedValue.Value

/-- Whole-program hook for an evidence-selected binary implementation method. -/
abbrev StagedValueRequiredBinaryElaborator (error : Type) :=
  ExpressionNode → ExpressionId → Syntax.BinaryOp → ExpressionId →
  Except error (StagedValueRequiredBinaryPlan error)

/-- Optional bridge used only by whole-program specialization consumers.
Source Core retains ownership of the lexical staged environment and of every
stage, type, traversal, and requirement-ledger check. -/
structure StagedValueLoweringPolicy (error : Type) where
  analysis : SourceStageAnalysis.Analysis
  onStagedValueCall : StagedValueCallElaborator error
  onStagedValueCoercion : StagedValueCoercionElaborator error
  onStagedValueRequiredUnary : StagedValueRequiredUnaryElaborator error
  onStagedValueRequiredBinary : StagedValueRequiredBinaryElaborator error

/-- A policy for a requirement-bearing unary expression declares the exact
type at which Source Core must check its operand, identifies the requirements
it discharges, and transforms the already recursively lowered operand. -/
structure RequiredUnaryPlan (error : Type) where
  operandType : Core.Ty
  consumedRequirements : List RequirementId
  build : Resolved.Expr → Except error Resolved.Expr

/-- A whole-program consumer may give runtime meaning to an otherwise staged,
requirement-bearing unary expression.  Source Core retains operand lookup,
coercion-aware traversal, type checking, and requirement reconciliation. -/
abbrev RequiredUnaryElaborator (error : Type) :=
  Resolved.Context → ExpressionNode → Syntax.UnaryOp → ExpressionId →
  Except error (RequiredUnaryPlan error)

/-- A policy for a requirement-bearing binary expression declares the exact
types at which Source Core must check its left and right children, identifies
the requirements discharged by the policy, and combines already recursively
lowered children.  The fixed-arity builder deliberately cannot traverse source
edges itself. -/
structure RequiredBinaryPlan (error : Type) where
  leftType : Core.Ty
  rightType : Core.Ty
  consumedRequirements : List RequirementId
  build : Resolved.Expr → Resolved.Expr → Except error Resolved.Expr

/-- A whole-program consumer may give runtime meaning to an otherwise staged,
requirement-bearing binary expression.  Source Core still owns child lookup,
left-to-right traversal, coercion-aware child lowering, type checking, and
requirement reconciliation. -/
abbrev RequiredBinaryElaborator (error : Type) :=
  Resolved.Context → ExpressionNode → ExpressionId → Syntax.BinaryOp →
  ExpressionId → Except error (RequiredBinaryPlan error)

/-- One executable coercion step declares both Core endpoints and the exact
requirement discharge it owns before transforming an already lowered source
expression.  Endpoint declarations keep malformed or stale policies from
silently assigning runtime meaning to a different typed path. -/
structure CoercionPlan (error : Type) where
  sourceType : Core.Ty
  targetType : Core.Ty
  consumedRequirements : List RequirementId
  build : Resolved.Expr → Except error Resolved.Expr

/-- A whole-program consumer may give runtime meaning to one evidence-bearing
coercion edge.  Source Core retains path validation, base-form traversal,
source-order composition, and exact requirement accounting. -/
abbrev CoercionElaborator (error : Type) :=
  Resolved.Context → ExpressionNode → CoercionStep →
  Except error (CoercionPlan error)

private def fail {alpha : Type} (site : ErrorSite) (reason : ErrorReason) :
    Except Error alpha :=
  .error { site, reason }

private def failWith {error alpha : Type} (lift : Error → error)
    (site : ErrorSite) (reason : ErrorReason) : Except error alpha :=
  .error (lift { site, reason })

private def nominalHead? : Ty → Option Resolved.DeclarationId
  | .constructor (.declaration id) => some id
  | .application function _ => nominalHead? function
  | _ => none

/-- Project exactly the closed builtin structural types admitted by this
bridge.  Source functions, nominal data, mappings and staging forms remain at
the specialization boundary. -/
def lowerType (site : ErrorSite) : Ty → Except Error Core.Ty
  | .variable id => fail site (.flexibleTypeVariable id)
  | .parameter id => fail site (.rigidTypeParameter id)
  | .constructor (.builtin .unit) => .ok .unit
  | .constructor (.builtin .bool) => .ok .bool
  | .constructor (.builtin .word) => .ok .word
  | type@(.constructor (.builtin .integer)) =>
      fail site (.unsupportedType type)
  | .constructor (.declaration id) => fail site (.nominalType id)
  | .product left right => do
      pure (.product (← lowerType site left) (← lowerType site right))
  | type@(.application _ _) =>
      match nominalHead? type with
      | some id => fail site (.nominalType id)
      | none => fail site (.unsupportedType type)
  | type@(.function _ _)
  | type@(.mapping _ _)
  | type@(.proxy _)
  | type@(.comptime _)
  | type@(.error) => fail site (.unsupportedType type)

private def lowerInputsAux (seen : List Resolved.LocalId) :
    List TypedBinder → Except Error Resolved.Context
  | [] => .ok []
  | binder :: rest => do
      if seen.contains binder.id then
        fail (.binder binder.id) (.duplicateInput binder.id)
      else if binder.scheme.quantified.isEmpty then
        let type ← lowerType (.binder binder.id) binder.scheme.body
        pure ((binder.id, type) :: (← lowerInputsAux (binder.id :: seen) rest))
      else
        fail (.binder binder.id) (.polymorphicInput binder.scheme.quantified)

private def lowerInputs (binders : List TypedBinder) :
    Except Error Resolved.Context :=
  lowerInputsAux [] binders

private def lookupExpression (source : TypedSource) (id : ExpressionId) :
    Except Error ExpressionNode :=
  match source.lookupNode? id.occurrence with
  | none => fail (.occurrence id.occurrence) .missingNode
  | some (.statement _) =>
      fail (.occurrence id.occurrence) .expectedExpressionNode
  | some (.expression node) => .ok node

private def lookupStatement (source : TypedSource) (id : StatementId) :
    Except Error StatementNode :=
  match source.lookupNode? id.occurrence with
  | none => fail (.occurrence id.occurrence) .missingNode
  | some (.expression _) =>
      fail (.occurrence id.occurrence) .expectedStatementNode
  | some (.statement node) => .ok node

private def directBinary (operator : Syntax.BinaryOp)
    (left right : Resolved.Expr) : Resolved.Expr :=
  match operator with
  | .multiply => .binary .wordMul left right
  | .divide => .binary .wordDiv left right
  | .modulo => .binary .wordMod left right
  | .add => .binary .wordAdd left right
  | .subtract => .binary .wordSub left right
  | .bitAnd => .binary .wordAnd left right
  | .bitXor => .binary .wordXor left right
  | .bitOr => .binary .wordOr left right
  | .greater => .binary .wordGt left right
  | .equal => .binary .wordEq left right
  | .less => .wordLt left right
  | .lessEqual => .unary .boolNot (.binary .wordGt left right)
  | .greaterEqual => .unary .boolNot (.wordLt left right)
  | .notEqual => .unary .boolNot (.binary .wordEq left right)
  | .logicalAnd => .ifE left right (.bool false)
  | .logicalOr => .ifE left (.bool true) right

private def productExpression : List Resolved.Expr → Resolved.Expr
  | [] => .unit
  | [element] => element
  | element :: rest => .pair element (productExpression rest)

private def ensureTypeWith {error : Type} (lift : Error → error)
    (site : ErrorSite) (expected : Core.Ty) (type : Ty) :
    Except error Unit := do
  let actual ← (lowerType site type).mapError lift
  if actual = expected then
    pure ()
  else
    failWith lift site (.typedNodeTypeMismatch expected actual)

private def exactIntegerLiteralRequirementWith {error : Type}
    (lift : Error → error) (site : ErrorSite)
    (solvedRequirements : List SolvedRequirement)
    (requirement : RequirementId) : Except error SolvedRequirement :=
  let candidates := solvedRequirements.filter fun solved =>
    decide (solved.id = requirement)
  match candidates with
  | [] => failWith lift site (.missingIntegerLiteralRequirement requirement)
  | [solved] => pure solved
  | solved =>
      failWith lift site
        (.duplicateIntegerLiteralRequirements requirement solved.length)

private structure ValidatedIntegerLiteral where
  rawValue : Nat
  consumedRequirements : List RequirementId

/-- Validate the source payload, stable requirement attachment, target-specific
builtin `Int` evidence, and premise-free primitive implementation shared by
runtime Word literals and staged integer evaluation.  `checkTarget` is invoked
after payload validation and before evidence lookup so each consumer retains
its own target-domain boundary without duplicating the carrier checks. -/
private def validateIntegerLiteralResolutionWith {error : Type}
    (lift : Error → error) (site : ErrorSite)
    (solvedRequirements : List SolvedRequirement) (nodeType : Ty)
    (attachedRequirements : List RequirementId)
    (source : Syntax.CoreLiteralValue)
    (resolution : IntegerLiteralResolution)
    (expectedImplementation : ProgramImplId)
    (checkTarget : Ty → Except error Unit) :
    Except error ValidatedIntegerLiteral := do
  if resolution.targetType != nodeType then
    failWith lift site
      (.integerLiteralTargetTypeMismatch resolution.targetType nodeType)
  else if attachedRequirements != [resolution.requirement] then
    failWith lift site
      (.integerLiteralRequirementsMismatch [resolution.requirement]
        attachedRequirements)
  else
    let decoded ← match numericLiteralValue? source with
      | none => failWith lift site (.invalidIntegerLiteralSource source)
      | some value => pure value
    if decoded != resolution.rawValue then
      failWith lift site
        (.integerLiteralRawValueMismatch decoded resolution.rawValue)
    else
      checkTarget resolution.targetType
      let expected := resolution.predicate
      let solved ← exactIntegerLiteralRequirementWith lift site
        solvedRequirements resolution.requirement
      if solved.predicate != expected then
        failWith lift site
          (.integerLiteralPredicateMismatch resolution.requirement expected
            solved.predicate)
      else if solved.evidence.goal != expected then
        failWith lift site
          (.integerLiteralEvidenceGoalMismatch resolution.requirement expected
            solved.evidence.goal)
      else
        match solved.evidence with
        | .assumption _ =>
            failWith lift site
              (.unresolvedIntegerLiteralEvidence resolution.requirement)
        | .implementation (.byImpl _ implementation premises) =>
            if implementation != expectedImplementation then
              failWith lift site
                (.integerLiteralImplementationMismatch
                  resolution.requirement expectedImplementation
                  implementation)
            else if !premises.isEmpty then
              failWith lift site
                (.integerLiteralPremiseCountMismatch
                  resolution.requirement 0 premises.length)
            else
              pure {
                rawValue := resolution.rawValue
                consumedRequirements := [resolution.requirement]
              }

/-- A Word literal whose exact builtin evidence and raw spelling were checked.
The requirement list records the obligations consumed by that validation. -/
structure WordIntegerLiteral where
  value : Core.Word
  consumedRequirements : List RequirementId
  deriving Repr, DecidableEq

/-- Shared metadata-only validation for runtime Word integer literals. This
does not traverse children, evaluate source code, or choose a user method. -/
def validateWordIntegerLiteralWith {error : Type}
    (lift : Error → error) (site : ErrorSite)
    (solvedRequirements : List SolvedRequirement) (nodeType : Ty)
    (attachedRequirements : List RequirementId)
    (source : Syntax.CoreLiteralValue)
    (resolution : IntegerLiteralResolution) :
    Except error WordIntegerLiteral := do
  let validated ← validateIntegerLiteralResolutionWith lift site
    solvedRequirements nodeType attachedRequirements source resolution
    (.builtin .intWord)
    (fun target => ensureTypeWith lift site .word target)
  pure {
    value := Core.Word.ofNatModulo validated.rawValue
    consumedRequirements := validated.consumedRequirements
  }

/-- The ordinary local compiler accepts the literal's own evidence, while
coercion execution remains outside this primitive interface. -/
def validateWordIntegerLiteral
    (solvedRequirements : List SolvedRequirement) (node : ExpressionNode)
    (source : Syntax.CoreLiteralValue) (resolution : IntegerLiteralResolution) :
    Except Error WordIntegerLiteral := do
  unless node.coercions.isEmpty do
    fail (.occurrence node.id.occurrence) (.coercionsPresent node.coercions)
  validateWordIntegerLiteralWith id (.occurrence node.id.occurrence)
    solvedRequirements node.type node.requirements source resolution

structure NativeIntegerLiteral where
  value : Int
  consumedRequirements : List RequirementId
  deriving Repr, DecidableEq

/-- Runtime Integer literals share the exact spelling, attachment and builtin
evidence validator with comptime and Word literals. This performs no evaluation. -/
def validateNativeIntegerLiteral
    (solvedRequirements : List SolvedRequirement) (node : ExpressionNode)
    (source : Syntax.CoreLiteralValue) (resolution : IntegerLiteralResolution) :
    Except Error NativeIntegerLiteral := do
  unless node.coercions.isEmpty do
    fail (.occurrence node.id.occurrence) (.coercionsPresent node.coercions)
  let validated ← validateIntegerLiteralResolutionWith id (.occurrence node.id.occurrence)
    solvedRequirements node.type node.requirements source resolution (.builtin .intInteger)
    (fun target => if target = Ty.integer then pure ()
      else fail (.occurrence node.id.occurrence) (.unsupportedType target))
  pure { value := Int.ofNat validated.rawValue, consumedRequirements := validated.consumedRequirements }

/-- Expression and pattern carriers share the same Word evidence validator. -/
private def lowerIntegerLiteralResolutionWith {error : Type}
    (lift : Error → error) (site : ErrorSite)
    (solvedRequirements : List SolvedRequirement) (nodeType : Ty)
    (attachedRequirements : List RequirementId)
    (source : Syntax.CoreLiteralValue)
    (resolution : IntegerLiteralResolution) :
    Except error LoweredExpression := do
  let validated ← validateWordIntegerLiteralWith lift site solvedRequirements
    nodeType attachedRequirements source resolution
  pure { resolved := .word validated.value, consumedRequirements := validated.consumedRequirements }

/-- Expression-node wrapper for the shared integer-literal validator. -/
private def lowerIntegerLiteralWith {error : Type} (lift : Error → error)
    (solvedRequirements : List SolvedRequirement) (node : ExpressionNode)
    (source : Syntax.CoreLiteralValue)
    (resolution : IntegerLiteralResolution) :
    Except error LoweredExpression :=
  lowerIntegerLiteralResolutionWith lift (.occurrence node.id.occurrence)
    solvedRequirements node.type node.requirements source resolution

/-- A closed staged integer and the exact literal obligations consumed while
computing it.  The signed value remains visible for direct executable tests;
only an explicit conversion or comparison projects the tree into runtime
Core. -/
structure StagedIntegerEvaluation where
  value : Int
  consumedRequirements : List RequirementId
  deriving Repr, DecidableEq

/-- A closed staged Word and the exact literal obligations consumed while
computing it.  The value is already canonical in `[0, 2^256)`. -/
structure StagedWordEvaluation where
  value : Core.Word
  consumedRequirements : List RequirementId
  deriving Repr, DecidableEq

/-- A closed staged Bool and the exact literal obligations consumed while
computing it.  Boolean staging is deliberately limited to builtin constants,
signed integer comparisons, transparent groups, and closed conditionals. -/
structure StagedBoolEvaluation where
  value : Bool
  consumedRequirements : List RequirementId
  deriving Repr, DecidableEq

/-- A Core-representable staged value together with the exact source
requirements consumed while producing it.  The separate bare-integer
evaluator remains the compatibility path for unbounded compile-time integers. -/
structure StagedValueEvaluation where
  value : SourceStagedValue.Value
  consumedRequirements : List RequirementId
  deriving Repr, DecidableEq

private structure StagedValueBinding where
  binder : TypedBinder
  value : SourceStagedValue.Value

private abbrev StagedValueEnvironment := List StagedValueBinding

private def StagedValueEnvironment.contains
    (environment : StagedValueEnvironment) (id : Resolved.LocalId) : Bool :=
  environment.any fun binding => decide (binding.binder.id = id)

private def StagedValueEnvironment.lookup?
    (environment : StagedValueEnvironment) (id : Resolved.LocalId) :
    Option StagedValueBinding :=
  environment.find? fun binding => decide (binding.binder.id = id)

/-- Internal late-bound evaluator used by the runtime lowerer.  Public callers
provide only the stage analysis and direct-call policy; this callback is built
inside Source Core after the staged evaluator has been defined. -/
private structure RawStagedValueLoweringPolicy (error : Type) where
  analysis : SourceStageAnalysis.Analysis
  evaluate : StagedValueEnvironment → ExpressionId →
    Except error StagedValueEvaluation

private structure StagedIntegerBinding where
  binder : TypedBinder
  value : Int

private abbrev StagedIntegerEnvironment := List StagedIntegerBinding

private def StagedIntegerEnvironment.contains
    (environment : StagedIntegerEnvironment) (id : Resolved.LocalId) : Bool :=
  environment.any fun binding => decide (binding.binder.id = id)

private def StagedIntegerEnvironment.lookup?
    (environment : StagedIntegerEnvironment) (id : Resolved.LocalId) :
    Option StagedIntegerBinding :=
  environment.find? fun binding => decide (binding.binder.id = id)

private inductive StagedIntegerBinaryOperation where
  | add
  | sub
  | mul

private def stagedIntegerBinaryOperation? :
    BuiltinFunctionId → Option StagedIntegerBinaryOperation
  | .integerAdd => some .add
  | .integerSub => some .sub
  | .integerMul => some .mul
  | _ => none

private def applyStagedIntegerBinary :
    StagedIntegerBinaryOperation → Int → Int → Int
  | .add, left, right => left + right
  | .sub, left, right => left - right
  | .mul, left, right => left * right

private inductive StagedIntegerComparison where
  | eq
  | lt

private def stagedIntegerComparison? :
    BuiltinFunctionId → Option StagedIntegerComparison
  | .integerEq => some .eq
  | .integerLt => some .lt
  | _ => none

private def applyStagedIntegerComparison :
    StagedIntegerComparison → Int → Int → Bool
  | .eq, left, right => decide (left = right)
  | .lt, left, right => decide (left < right)

private def builtinBooleanSpelling (value : Bool) : String :=
  if value then "true" else "false"

private def validateBuiltinFunctionArgumentTypesWith {error : Type}
    (lift : Error → error) (source : TypedSource)
    (function : BuiltinFunctionId) :
    Nat → List Ty → List ExpressionId → Except error Unit
  | _, [], [] => pure ()
  | index, expected :: expectedRest, argument :: argumentRest => do
      let node ← (lookupExpression source argument).mapError lift
      if node.type != expected then
        failWith lift (.occurrence argument.occurrence)
          (.builtinFunctionArgumentTypeMismatch function index expected
            node.type)
      else
        validateBuiltinFunctionArgumentTypesWith lift source function
          (index + 1) expectedRest argumentRest
  | _, _, _ =>
      -- The caller checks arity before entering this exact positional walk.
      failWith lift (.declaration source.owner)
        (.builtinFunctionArgumentArityMismatch function
          function.parameterTypes.length 0)

/-- Recheck the complete synthetic callee and fixed signature attached by
source inference.  Compiler functions have no source declaration identity,
requirements, coercions, or specialization edge. -/
private def validateBuiltinFunctionCallWith {error : Type}
    (lift : Error → error) (source : TypedSource)
    (node : ExpressionNode) (callee : ExpressionId)
    (arguments : List ExpressionId) (function : BuiltinFunctionId) :
    Except error Unit := do
  let site := ErrorSite.occurrence node.id.occurrence
  unless node.requirements.isEmpty do
    failWith lift site
      (.builtinFunctionRequirementsPresent function node.requirements)
  unless node.coercions.isEmpty do
    failWith lift site
      (.builtinFunctionCoercionsPresent function node.coercions)
  if node.type != function.returnType then
    failWith lift site
      (.builtinFunctionCallTypeMismatch function function.returnType node.type)
  unless arguments.length = function.parameterTypes.length do
    failWith lift site
      (.builtinFunctionArgumentArityMismatch function
        function.parameterTypes.length arguments.length)
  let calleeNode ← (lookupExpression source callee).mapError lift
  let calleeSite := ErrorSite.occurrence callee.occurrence
  unless calleeNode.requirements.isEmpty do
    failWith lift calleeSite (.requirementsPresent calleeNode.requirements)
  unless calleeNode.coercions.isEmpty do
    failWith lift calleeSite (.coercionsPresent calleeNode.coercions)
  match calleeNode.form with
  | .reference name (.builtinFunction actual) =>
      if actual != function then
        failWith lift calleeSite
          (.builtinFunctionCalleeIdentityMismatch function actual)
      else if name != function.spelling then
        failWith lift calleeSite
          (.builtinFunctionCalleeSpellingMismatch function function.spelling
            name)
      else if calleeNode.type != function.type then
        failWith lift calleeSite
          (.builtinFunctionCalleeTypeMismatch function function.type
            calleeNode.type)
      else
        validateBuiltinFunctionArgumentTypesWith lift source function 0
          function.parameterTypes arguments
  | _ =>
      failWith lift calleeSite (.builtinFunctionCalleeNotReference function)

private def validateStagedIntegerBinderWith {error : Type}
    (lift : Error → error) (site : ErrorSite) (source : TypedSource)
    (binder : TypedBinder) : Except error Unit := do
  if binder.id.owner != source.owner then
    failWith lift site (.ownerMismatch source.owner binder.id.owner)
  else if !binder.scheme.quantified.isEmpty then
    failWith lift site (.polymorphicLocal binder.scheme.quantified)
  else if binder.scheme.body != Ty.integer then
    failWith lift site
      (.stagedIntegerTypeMismatch .integer binder.scheme.body)
  else
    pure ()

/-- Metadata-only authentication usable by runtime Core lowering as well as
the staged evaluator. The compiler preserves the existing call validation. -/
def validateBuiltinFunctionCall (source : TypedSource) (node : ExpressionNode)
    (callee : ExpressionId) (arguments : List ExpressionId) (function : BuiltinFunctionId) :
    Except Error Unit :=
  validateBuiltinFunctionCallWith id source node callee arguments function

mutual

private def evaluateStagedIntegerFuelWith {error : Type}
    (lift : Error → error)
    (onStagedIntegerCall : StagedIntegerCallElaborator error)
    (solvedRequirements : List SolvedRequirement)
    (source : TypedSource) (environment : StagedIntegerEnvironment)
    (execute : Bool) :
    Nat → ExpressionId → Except error StagedIntegerEvaluation
  | 0, id =>
      failWith lift (.occurrence id.occurrence) .stagedIntegerDepthLimit
  | fuel + 1, id => do
      let node ← (lookupExpression source id).mapError lift
      let site := ErrorSite.occurrence id.occurrence
      match node.form with
      | .call callee arguments (.builtinFunction .wordToInteger) => do
          validateBuiltinFunctionCallWith lift source node callee arguments
            .wordToInteger
          match arguments with
          | [argument] =>
              let evaluated ← evaluateStagedWordFuelWith lift
                onStagedIntegerCall
                solvedRequirements source environment execute fuel argument
              pure {
                value := if execute then Int.ofNat evaluated.value.val else 0
                consumedRequirements := evaluated.consumedRequirements
              }
          | _ =>
              failWith lift site
                (.builtinFunctionArgumentArityMismatch .wordToInteger 1
                  arguments.length)
      | .call callee arguments (.builtinFunction function) =>
          match stagedIntegerBinaryOperation? function with
          | some operation => do
              validateBuiltinFunctionCallWith lift source node callee arguments
                function
              match arguments with
              | [left, right] =>
                  let left ← evaluateStagedIntegerFuelWith lift
                    onStagedIntegerCall
                    solvedRequirements source environment execute fuel left
                  let right ← evaluateStagedIntegerFuelWith lift
                    onStagedIntegerCall
                    solvedRequirements source environment execute fuel right
                  pure {
                    value := if execute then
                      applyStagedIntegerBinary operation left.value right.value
                    else 0
                    consumedRequirements := left.consumedRequirements ++
                      right.consumedRequirements
                  }
              | _ =>
                  failWith lift site
                    (.builtinFunctionArgumentArityMismatch function 2
                      arguments.length)
          | none => do
              unless node.coercions.isEmpty do
                failWith lift site (.coercionsPresent node.coercions)
              if node.type != Ty.integer then
                failWith lift site
                  (.stagedIntegerTypeMismatch .integer node.type)
              else
                failWith lift site .stagedIntegerExpressionNotClosed
      | .call callee arguments (.declaration instantiation) => do
          unless node.coercions.isEmpty do
            failWith lift site (.coercionsPresent node.coercions)
          if node.type != Ty.integer then
            failWith lift site (.stagedIntegerTypeMismatch .integer node.type)
          let plan ← onStagedIntegerCall node callee arguments instantiation
          if plan.consumedRequirements != node.requirements then
            failWith lift site
              (.stagedIntegerCallRequirementsMismatch node.requirements
                plan.consumedRequirements)
          else if plan.argumentTypes.length != arguments.length then
            failWith lift site
              (.stagedIntegerCallArgumentArityMismatch
                plan.argumentTypes.length arguments.length)
          else
            let evaluatedArguments ←
              (plan.argumentTypes.zip arguments).mapM fun pair => do
                let argumentNode ←
                  (lookupExpression source pair.2).mapError lift
                if pair.1 != Ty.integer then
                  failWith lift (.occurrence pair.2.occurrence)
                    (.stagedIntegerTypeMismatch .integer pair.1)
                else if argumentNode.type != pair.1 then
                  failWith lift (.occurrence pair.2.occurrence)
                    (.stagedIntegerTypeMismatch pair.1 argumentNode.type)
                else
                  evaluateStagedIntegerFuelWith lift onStagedIntegerCall
                    solvedRequirements source environment execute fuel pair.2
            let value ← if execute then
                plan.invoke
                  (evaluatedArguments.map fun argument => argument.value)
              else
                pure 0
            pure {
              value
              consumedRequirements := evaluatedArguments.flatMap
                (fun argument => argument.consumedRequirements) ++
                plan.consumedRequirements
            }
      | form => do
          unless node.coercions.isEmpty do
            failWith lift site (.coercionsPresent node.coercions)
          if node.type != Ty.integer then
            failWith lift site (.stagedIntegerTypeMismatch .integer node.type)
          match form with
          | .integerLiteral literal resolution =>
              let validated ← validateIntegerLiteralResolutionWith lift site
                solvedRequirements node.type node.requirements literal resolution
                (.builtin .intInteger)
                (fun target =>
                  if target = Ty.integer then pure ()
                  else failWith lift site
                    (.stagedIntegerTypeMismatch .integer target))
              pure {
                value := Int.ofNat validated.rawValue
                consumedRequirements := validated.consumedRequirements
              }
          | .reference name (.local binder) => do
              unless node.requirements.isEmpty do
                failWith lift site (.requirementsPresent node.requirements)
              if binder.owner != source.owner then
                failWith lift site (.ownerMismatch source.owner binder.owner)
              let binding ← match environment.lookup? binder with
                | some binding => pure binding
                | none => failWith lift site (.unknownLocal binder)
              validateStagedIntegerBinderWith lift site source binding.binder
              if name != binding.binder.name then
                failWith lift site
                  (.stagedIntegerLocalSpellingMismatch binder
                    binding.binder.name name)
              pure {
                value := binding.value
                consumedRequirements := []
              }
          | .group inner =>
              if node.requirements.isEmpty then
                evaluateStagedIntegerFuelWith lift onStagedIntegerCall
                  solvedRequirements source environment execute fuel inner
              else
                failWith lift site (.requirementsPresent node.requirements)
          | .conditional condition thenBranch elseBranch => do
              unless node.requirements.isEmpty do
                failWith lift site (.requirementsPresent node.requirements)
              let condition ← evaluateStagedBoolFuelWith lift
                onStagedIntegerCall
                solvedRequirements source environment execute fuel condition
              let thenBranch ← evaluateStagedIntegerFuelWith lift
                onStagedIntegerCall
                solvedRequirements source environment
                  (execute && condition.value) fuel thenBranch
              let elseBranch ← evaluateStagedIntegerFuelWith lift
                onStagedIntegerCall
                solvedRequirements source environment
                  (execute && !condition.value) fuel elseBranch
              pure {
                value := if condition.value then thenBranch.value
                  else elseBranch.value
                consumedRequirements :=
                  condition.consumedRequirements ++
                  thenBranch.consumedRequirements ++
                  elseBranch.consumedRequirements
              }
          | _ =>
              failWith lift site .stagedIntegerExpressionNotClosed

private def evaluateStagedWordFuelWith {error : Type}
    (lift : Error → error)
    (onStagedIntegerCall : StagedIntegerCallElaborator error)
    (solvedRequirements : List SolvedRequirement)
    (source : TypedSource) (environment : StagedIntegerEnvironment)
    (execute : Bool) :
    Nat → ExpressionId → Except error StagedWordEvaluation
  | 0, id =>
      failWith lift (.occurrence id.occurrence) .stagedWordDepthLimit
  | fuel + 1, id => do
      let node ← (lookupExpression source id).mapError lift
      let site := ErrorSite.occurrence id.occurrence
      match node.form with
      | .call callee arguments (.builtinFunction .wordFromInteger) => do
          validateBuiltinFunctionCallWith lift source node callee arguments
            .wordFromInteger
          match arguments with
          | [argument] =>
              let evaluated ← evaluateStagedIntegerFuelWith lift
                onStagedIntegerCall
                solvedRequirements source environment execute fuel argument
              pure {
                value := if execute then Core.Word.ofIntModulo evaluated.value
                  else Core.Word.ofNatModulo 0
                consumedRequirements := evaluated.consumedRequirements
              }
          | _ =>
              failWith lift site
                (.builtinFunctionArgumentArityMismatch .wordFromInteger 1
                  arguments.length)
      | form => do
          unless node.coercions.isEmpty do
            failWith lift site (.coercionsPresent node.coercions)
          if node.type != Ty.word then
            failWith lift site (.stagedWordTypeMismatch .word node.type)
          match form with
          | .integerLiteral literal resolution =>
              let validated ← validateIntegerLiteralResolutionWith lift site
                solvedRequirements node.type node.requirements literal resolution
                (.builtin .intWord)
                (fun target =>
                  if target = Ty.word then pure ()
                  else failWith lift site
                    (.stagedWordTypeMismatch .word target))
              pure {
                value := Core.Word.ofNatModulo validated.rawValue
                consumedRequirements := validated.consumedRequirements
              }
          | .group inner =>
              if node.requirements.isEmpty then
                evaluateStagedWordFuelWith lift onStagedIntegerCall
                  solvedRequirements source environment execute fuel inner
              else
                failWith lift site (.requirementsPresent node.requirements)
          | .conditional condition thenBranch elseBranch => do
              unless node.requirements.isEmpty do
                failWith lift site (.requirementsPresent node.requirements)
              let condition ← evaluateStagedBoolFuelWith lift
                onStagedIntegerCall
                solvedRequirements source environment execute fuel condition
              let thenBranch ← evaluateStagedWordFuelWith lift
                onStagedIntegerCall
                solvedRequirements source environment
                  (execute && condition.value) fuel thenBranch
              let elseBranch ← evaluateStagedWordFuelWith lift
                onStagedIntegerCall
                solvedRequirements source environment
                  (execute && !condition.value) fuel elseBranch
              pure {
                value := if condition.value then thenBranch.value
                  else elseBranch.value
                consumedRequirements :=
                  condition.consumedRequirements ++
                  thenBranch.consumedRequirements ++
                  elseBranch.consumedRequirements
              }
          | _ =>
              failWith lift site .stagedWordExpressionNotClosed

private def evaluateStagedBoolFuelWith {error : Type}
    (lift : Error → error)
    (onStagedIntegerCall : StagedIntegerCallElaborator error)
    (solvedRequirements : List SolvedRequirement)
    (source : TypedSource) (environment : StagedIntegerEnvironment)
    (execute : Bool) :
    Nat → ExpressionId → Except error StagedBoolEvaluation
  | 0, id =>
      failWith lift (.occurrence id.occurrence) .stagedBoolDepthLimit
  | fuel + 1, id => do
      let node ← (lookupExpression source id).mapError lift
      let site := ErrorSite.occurrence id.occurrence
      match node.form with
      | .call callee arguments (.builtinFunction function) =>
          match stagedIntegerComparison? function with
          | some comparison => do
              validateBuiltinFunctionCallWith lift source node callee arguments
                function
              match arguments with
              | [left, right] =>
                  let left ← evaluateStagedIntegerFuelWith lift
                    onStagedIntegerCall
                    solvedRequirements source environment execute fuel left
                  let right ← evaluateStagedIntegerFuelWith lift
                    onStagedIntegerCall
                    solvedRequirements source environment execute fuel right
                  pure {
                    value := if execute then
                      applyStagedIntegerComparison comparison left.value
                        right.value
                    else false
                    consumedRequirements := left.consumedRequirements ++
                      right.consumedRequirements
                  }
              | _ =>
                  failWith lift site
                    (.builtinFunctionArgumentArityMismatch function 2
                      arguments.length)
          | none => do
              unless node.coercions.isEmpty do
                failWith lift site (.coercionsPresent node.coercions)
              if node.type != Ty.bool then
                failWith lift site (.stagedBoolTypeMismatch .bool node.type)
              unless node.requirements.isEmpty do
                failWith lift site (.requirementsPresent node.requirements)
              failWith lift site .stagedBoolExpressionNotClosed
      | form => do
          unless node.coercions.isEmpty do
            failWith lift site (.coercionsPresent node.coercions)
          if node.type != Ty.bool then
            failWith lift site (.stagedBoolTypeMismatch .bool node.type)
          unless node.requirements.isEmpty do
            failWith lift site (.requirementsPresent node.requirements)
          match form with
          | .reference name (.builtinBoolean value) =>
              let expected := builtinBooleanSpelling value
              if name = expected then
                pure { value, consumedRequirements := [] }
              else
                failWith lift site
                  (.builtinBooleanSpellingMismatch value expected name)
          | .group inner =>
              evaluateStagedBoolFuelWith lift onStagedIntegerCall
                solvedRequirements source environment execute fuel inner
          | .conditional condition thenBranch elseBranch => do
              let condition ← evaluateStagedBoolFuelWith lift
                onStagedIntegerCall solvedRequirements source environment
                execute fuel condition
              let thenBranch ← evaluateStagedBoolFuelWith lift
                onStagedIntegerCall solvedRequirements source environment
                (execute && condition.value) fuel thenBranch
              let elseBranch ← evaluateStagedBoolFuelWith lift
                onStagedIntegerCall solvedRequirements source environment
                (execute && !condition.value) fuel elseBranch
              pure {
                value := if condition.value then thenBranch.value
                  else elseBranch.value
                consumedRequirements := condition.consumedRequirements ++
                  thenBranch.consumedRequirements ++
                  elseBranch.consumedRequirements
              }
          | _ => failWith lift site .stagedBoolExpressionNotClosed

end

private def rejectStagedIntegerCallsWith {error : Type}
    (lift : Error → error) : StagedIntegerCallElaborator error :=
  fun node _ _ _ =>
    failWith lift (.occurrence node.id.occurrence)
      .stagedIntegerExpressionNotClosed

private def rejectStagedValueCallsWith {error : Type}
    (lift : Error → error) : StagedValueCallElaborator error :=
  fun node _ _ _ =>
    if !node.requirements.isEmpty then
      failWith lift (.occurrence node.id.occurrence)
        (.requirementsPresent node.requirements)
    else
      failWith lift (.occurrence node.id.occurrence)
        (.unsupportedExpression .call)

private def rejectStagedValueCoercionsWith {error : Type}
    (lift : Error → error) : StagedValueCoercionElaborator error :=
  fun node _ =>
    failWith lift (.occurrence node.id.occurrence)
      (.coercionsPresent node.coercions)

private def rejectStagedValueRequiredUnariesWith {error : Type}
    (lift : Error → error) : StagedValueRequiredUnaryElaborator error :=
  fun node _ _ =>
    failWith lift (.occurrence node.id.occurrence)
      (.requirementsPresent node.requirements)

private def rejectStagedValueRequiredBinariesWith {error : Type}
    (lift : Error → error) : StagedValueRequiredBinaryElaborator error :=
  fun node _ _ _ =>
    failWith lift (.occurrence node.id.occurrence)
      (.requirementsPresent node.requirements)

/-- Evaluate staged integer expressions with an explicit whole-program direct
call policy.  Structural expression fuel remains source-local; recursive call
fuel and specialization-cycle tracking belong to the policy's owner. -/
def evaluateStagedIntegerWith {error : Type} (lift : Error → error)
    (onStagedIntegerCall : StagedIntegerCallElaborator error)
    (solvedRequirements : List SolvedRequirement)
    (source : TypedSource) (id : ExpressionId) :
    Except error StagedIntegerEvaluation :=
  evaluateStagedIntegerFuelWith lift onStagedIntegerCall solvedRequirements
    source [] true (source.nodes.length + 1) id

/-- Evaluate staged Word expressions while allowing nested staged-integer
source calls only through the supplied policy. -/
def evaluateStagedWordWith {error : Type} (lift : Error → error)
    (onStagedIntegerCall : StagedIntegerCallElaborator error)
    (solvedRequirements : List SolvedRequirement)
    (source : TypedSource) (id : ExpressionId) :
    Except error StagedWordEvaluation :=
  evaluateStagedWordFuelWith lift onStagedIntegerCall solvedRequirements source
    [] true (source.nodes.length + 1) id

/-- Evaluate staged Bool expressions while allowing nested staged-integer
source calls only through the supplied policy. -/
def evaluateStagedBoolWith {error : Type} (lift : Error → error)
    (onStagedIntegerCall : StagedIntegerCallElaborator error)
    (solvedRequirements : List SolvedRequirement)
    (source : TypedSource) (id : ExpressionId) :
    Except error StagedBoolEvaluation :=
  evaluateStagedBoolFuelWith lift onStagedIntegerCall solvedRequirements source
    [] true (source.nodes.length + 1) id

/-- Evaluate exactly the closed staged-integer fragment accepted by runtime
erasure, including conversions through the closed staged-Word fragment.  The
bound comes from the finite typed-node table, so malformed cycles produce a
located failure rather than nontermination. -/
def evaluateStagedInteger (solvedRequirements : List SolvedRequirement)
    (source : TypedSource) (id : ExpressionId) :
    Except Error StagedIntegerEvaluation :=
  evaluateStagedIntegerWith (fun error => error)
    (rejectStagedIntegerCallsWith (fun error => error))
    solvedRequirements source id

/-- Evaluate exactly the closed staged-Word fragment accepted by
`wordToInteger`.  Cross-domain cycles share the same finite node-derived fuel
as staged-integer evaluation. -/
def evaluateStagedWord (solvedRequirements : List SolvedRequirement)
    (source : TypedSource) (id : ExpressionId) :
    Except Error StagedWordEvaluation :=
  evaluateStagedWordWith (fun error => error)
    (rejectStagedIntegerCallsWith (fun error => error))
    solvedRequirements source id

/-- Evaluate the closed staged-Bool fragment used by integer and Word
conditionals.  All three conditional children are validated under the same
finite node-derived depth bound even though only one branch supplies the
result, preserving declaration-wide exact requirement accounting. -/
def evaluateStagedBool (solvedRequirements : List SolvedRequirement)
    (source : TypedSource) (id : ExpressionId) :
    Except Error StagedBoolEvaluation :=
  evaluateStagedBoolWith (fun error => error)
    (rejectStagedIntegerCallsWith (fun error => error))
    solvedRequirements source id

private def lowerWordFromIntegerWith {error : Type} (lift : Error → error)
    (onStagedIntegerCall : StagedIntegerCallElaborator error)
    (solvedRequirements : List SolvedRequirement) (source : TypedSource)
    (environment : StagedIntegerEnvironment)
    (fuel : Nat) (node : ExpressionNode) (callee : ExpressionId)
    (arguments : List ExpressionId) : Except error LoweredExpression := do
  validateBuiltinFunctionCallWith lift source node callee arguments
    .wordFromInteger
  match arguments with
  | [argument] =>
      let evaluated ← evaluateStagedIntegerFuelWith lift
        onStagedIntegerCall solvedRequirements source environment true fuel
        argument
      pure {
        resolved := .word (Core.Word.ofIntModulo evaluated.value)
        consumedRequirements := evaluated.consumedRequirements
      }
  | _ =>
      failWith lift (.occurrence node.id.occurrence)
        (.builtinFunctionArgumentArityMismatch .wordFromInteger 1
          arguments.length)

private def lowerStagedBoolWith {error : Type} (lift : Error → error)
    (onStagedIntegerCall : StagedIntegerCallElaborator error)
    (solvedRequirements : List SolvedRequirement) (source : TypedSource)
    (environment : StagedIntegerEnvironment)
    (fuel : Nat) (id : ExpressionId) : Except error LoweredExpression := do
  let evaluated ← evaluateStagedBoolFuelWith lift onStagedIntegerCall
    solvedRequirements source environment true fuel id
  pure {
    resolved := .bool evaluated.value
    consumedRequirements := evaluated.consumedRequirements
  }

private def eraseRequirement? (target : RequirementId) :
    List RequirementId → Option (List RequirementId)
  | [] => none
  | requirement :: rest =>
      if requirement = target then
        some rest
      else
        (eraseRequirement? target rest).map fun remaining =>
          requirement :: remaining

private structure PreparedCoercionPath where
  rawType : Ty
  remainingRequirements : List RequirementId

private def consumeCoercionRequirementWith {error : Type}
    (lift : Error → error) (site : ErrorSite)
    (attached : List RequirementId) (seen : List RequirementId)
    (remaining : List RequirementId) (requirement : RequirementId) :
    Except error (List RequirementId) :=
  if seen.contains requirement then
    failWith lift site (.duplicateCoercionRequirement requirement)
  else
    match eraseRequirement? requirement remaining with
    | none =>
        failWith lift site (.missingCoercionRequirement requirement attached)
    | some result =>
        if result.contains requirement then
          failWith lift site (.duplicateCoercionRequirement requirement)
        else
          pure result

private def consumeCoercionRequirementsWith {error : Type}
    (lift : Error → error) (site : ErrorSite)
    (attached : List RequirementId) :
    List RequirementId → List RequirementId → List RequirementId →
      Except error (List RequirementId × List RequirementId)
  | [], seen, remaining => pure (seen, remaining)
  | requirement :: requirements, seen, remaining => do
      let remaining ← consumeCoercionRequirementWith lift site attached
        seen remaining requirement
      consumeCoercionRequirementsWith lift site attached requirements
        (requirement :: seen) remaining

private def prepareCoercionTailWith {error : Type}
    (lift : Error → error) (site : ErrorSite)
    (attached : List RequirementId) (finalType : Ty) :
    Nat → Ty → List RequirementId → List RequirementId →
      List CoercionStep → Except error (List RequirementId)
  | _, previousTarget, _, remaining, [] =>
      if previousTarget = finalType then
        pure remaining
      else
        failWith lift site
          (.coercionPathTargetMismatch finalType previousTarget)
  | index, previousTarget, seen, remaining, step :: rest => do
      if step.source != previousTarget then
        failWith lift site
          (.coercionPathDiscontinuity index previousTarget step.source)
      else if step.source = step.target then
        failWith lift site
          (.identityCoercionStep index step.requirement step.source)
      else
        let (seen, remaining) ← consumeCoercionRequirementsWith lift site
          attached step.requirements seen remaining
        prepareCoercionTailWith lift site attached finalType (index + 1)
          step.target seen remaining rest

private def prepareCoercionPathWith {error : Type}
    (lift : Error → error) (node : ExpressionNode)
    (first : CoercionStep) (rest : List CoercionStep) :
    Except error PreparedCoercionPath := do
  let site := ErrorSite.occurrence node.id.occurrence
  if first.source = first.target then
    failWith lift site
      (.identityCoercionStep 0 first.requirement first.source)
  else
    let (seen, remaining) ← consumeCoercionRequirementsWith lift site
      node.requirements first.requirements [] node.requirements
    let remaining ← prepareCoercionTailWith lift site node.requirements
      node.type 1 first.target seen remaining rest
    pure {
      rawType := first.source
      remainingRequirements := remaining
    }

private def checkedCoercionPlansWith {error : Type}
    (lift : Error → error) (onCoercion : CoercionElaborator error)
    (scope : Resolved.Context) (node : ExpressionNode) :
    List CoercionStep → Except error (List (CoercionPlan error))
  | [] => pure []
  | step :: rest => do
      let sourceType ←
        (lowerType (.occurrence node.id.occurrence) step.source).mapError lift
      let targetType ←
        (lowerType (.occurrence node.id.occurrence) step.target).mapError lift
      let plan ← onCoercion scope node step
      if plan.sourceType != sourceType then
        failWith lift (.occurrence node.id.occurrence)
          (.coercionPlanSourceTypeMismatch step.requirement sourceType
            plan.sourceType)
      else if plan.targetType != targetType then
        failWith lift (.occurrence node.id.occurrence)
          (.coercionPlanTargetTypeMismatch step.requirement targetType
            plan.targetType)
      else if plan.consumedRequirements != step.requirements then
        failWith lift (.occurrence node.id.occurrence)
          (.coercionPlanRequirementsMismatch step.requirement
            step.requirements plan.consumedRequirements)
      else
        pure (plan :: (← checkedCoercionPlansWith lift onCoercion scope
          node rest))

private def applyCoercionPlans {error : Type}
    (resolved : Resolved.Expr) (consumed : List RequirementId) :
    List (CoercionPlan error) → Except error LoweredExpression
  | [] => pure { resolved, consumedRequirements := consumed }
  | plan :: rest => do
      let resolved ← plan.build resolved
      applyCoercionPlans resolved
        (consumed ++ plan.consumedRequirements) rest

private structure CheckedStagedValueCoercionPlan (error : Type) where
  requirement : RequirementId
  plan : StagedValueCoercionPlan error

/-- Validate staged coercion policy metadata against the same canonical path
used by ordinary lowering. -/
private def checkedStagedValueCoercionPlansWith {error : Type}
    (lift : Error → error)
    (onCoercion : StagedValueCoercionElaborator error)
    (node : ExpressionNode) :
    List CoercionStep →
      Except error (List (CheckedStagedValueCoercionPlan error))
  | [] => pure []
  | step :: rest => do
      let sourceType ←
        (lowerType (.occurrence node.id.occurrence) step.source).mapError lift
      let targetType ←
        (lowerType (.occurrence node.id.occurrence) step.target).mapError lift
      let plan ← onCoercion node step
      if plan.sourceType != sourceType then
        failWith lift (.occurrence node.id.occurrence)
          (.coercionPlanSourceTypeMismatch step.requirement sourceType
            plan.sourceType)
      else if plan.targetType != targetType then
        failWith lift (.occurrence node.id.occurrence)
          (.coercionPlanTargetTypeMismatch step.requirement targetType
            plan.targetType)
      else if plan.consumedRequirements != step.requirements then
        failWith lift (.occurrence node.id.occurrence)
          (.coercionPlanRequirementsMismatch step.requirement
            step.requirements plan.consumedRequirements)
      else
        pure ({ requirement := step.requirement, plan } ::
          (← checkedStagedValueCoercionPlansWith lift onCoercion node rest))

/-- Execute a validated staged coercion path in source order, checking both
value endpoints and retaining the exact requirement discharge order. -/
private def applyStagedValueCoercionPlansWith {error : Type}
    (lift : Error → error) (site : ErrorSite)
    (value : SourceStagedValue.Value) (consumed : List RequirementId) :
    List (CheckedStagedValueCoercionPlan error) →
      Except error StagedValueEvaluation
  | [] => pure { value, consumedRequirements := consumed }
  | checked :: rest => do
      let actualSource := SourceStagedValue.coreType value
      if actualSource != checked.plan.sourceType then
        failWith lift site
          (.coercionPlanSourceTypeMismatch checked.requirement
            checked.plan.sourceType actualSource)
      let value ← checked.plan.invoke value
      let actualTarget := SourceStagedValue.coreType value
      if actualTarget != checked.plan.targetType then
        failWith lift site
          (.coercionPlanTargetTypeMismatch checked.requirement
            checked.plan.targetType actualTarget)
      applyStagedValueCoercionPlansWith lift site value
        (consumed ++ checked.plan.consumedRequirements) rest

/-- Lower one coercion-cleared expression node.  Recursive edges return to the
outer traversal, so every child independently receives its own coercion policy
without reapplying the current node's path. -/
private def lowerExpressionNodeWith {error : Type} (lift : Error → error)
    (onCall : StagedAwareCallElaborator error)
    (stagedValueArgument : StagedValueArgumentOracle error)
    (onRequiredUnary : RequiredUnaryElaborator error)
    (onRequiredBinary : RequiredBinaryElaborator error)
    (solvedRequirements : List SolvedRequirement)
    (source : TypedSource) (scope : Resolved.Context)
    (recurse : ExpressionId → Except error LoweredExpression)
    (node : ExpressionNode) : Except error LoweredExpression :=
  let id := node.id
  match node.form with
  | .integerLiteral source resolution =>
      lowerIntegerLiteralWith lift solvedRequirements node source resolution
  | .call callee arguments resolution => do
      let plan ← onCall stagedValueArgument scope node callee arguments
        resolution
      if plan.consumedRequirements != node.requirements then
        failWith lift (.occurrence id.occurrence)
          (.callRequirementsMismatch node.requirements
            plan.consumedRequirements)
      else if plan.argumentTypes.length != arguments.length then
        failWith lift (.occurrence id.occurrence)
          (.callArgumentArityMismatch plan.argumentTypes.length
            arguments.length)
      else
        let loweredArguments ←
          (plan.argumentTypes.zip arguments).mapM fun pair => do
            let argumentNode ←
              (lookupExpression source pair.2).mapError lift
            ensureTypeWith lift (.occurrence pair.2.occurrence)
              pair.1 argumentNode.type
            recurse pair.2
        let resolved ← plan.build
          (loweredArguments.map fun argument => argument.resolved)
        pure {
          resolved
          consumedRequirements :=
            loweredArguments.flatMap
              (fun argument => argument.consumedRequirements) ++
            plan.consumedRequirements
        }
  | .unary operator operand =>
      if node.requirements.isEmpty then
        match lowerType (.occurrence id.occurrence) node.type with
        | .error error => .error (lift error)
        | .ok _ => do
            let operand ← recurse operand
            pure {
              resolved := match operator with
                | .logicalNot => .unary .boolNot operand.resolved
                | .bitNot => .unary .wordNot operand.resolved
              consumedRequirements := operand.consumedRequirements
            }
      else do
        let plan ← onRequiredUnary scope node operator operand
        if plan.consumedRequirements != node.requirements then
          failWith lift (.occurrence id.occurrence)
            (.unaryRequirementsMismatch node.requirements
              plan.consumedRequirements)
        else
          match lowerType (.occurrence id.occurrence) node.type with
          | .error error => .error (lift error)
          | .ok _ =>
            let operandNode ← (lookupExpression source operand).mapError lift
            ensureTypeWith lift (.occurrence operand.occurrence)
              plan.operandType operandNode.type
            let loweredOperand ← recurse operand
            let resolved ← plan.build loweredOperand.resolved
            pure {
              resolved
              consumedRequirements := loweredOperand.consumedRequirements ++
                plan.consumedRequirements
            }
  | .binary left operator right =>
      if node.requirements.isEmpty then
        match lowerType (.occurrence id.occurrence) node.type with
        | .error error => .error (lift error)
        | .ok _ => do
            let left ← recurse left
            let right ← recurse right
            pure {
              resolved := directBinary operator left.resolved right.resolved
              consumedRequirements := left.consumedRequirements ++
                right.consumedRequirements
            }
      else do
        let plan ← onRequiredBinary scope node left operator right
        if plan.consumedRequirements != node.requirements then
          failWith lift (.occurrence id.occurrence)
            (.binaryRequirementsMismatch node.requirements
              plan.consumedRequirements)
        else
          match lowerType (.occurrence id.occurrence) node.type with
          | .error error => .error (lift error)
          | .ok _ =>
            let leftNode ← (lookupExpression source left).mapError lift
            ensureTypeWith lift (.occurrence left.occurrence)
              plan.leftType leftNode.type
            let loweredLeft ← recurse left
            let rightNode ← (lookupExpression source right).mapError lift
            ensureTypeWith lift (.occurrence right.occurrence)
              plan.rightType rightNode.type
            let loweredRight ← recurse right
            let resolved ← plan.build loweredLeft.resolved
              loweredRight.resolved
            pure {
              resolved
              consumedRequirements :=
                loweredLeft.consumedRequirements ++
                loweredRight.consumedRequirements ++
                plan.consumedRequirements
            }
  | _ =>
      if !node.requirements.isEmpty then
        failWith lift (.occurrence id.occurrence)
          (.requirementsPresent node.requirements)
      else
        match lowerType (.occurrence id.occurrence) node.type with
        | .error error => .error (lift error)
        | .ok _ =>
          match node.form with
          | .literal literal =>
              match interpretWordLiteral? ⟨node.span, literal⟩ with
              | some word => pure {
                  resolved := .word word
                  consumedRequirements := []
                }
              | none =>
                  failWith lift (.occurrence id.occurrence)
                    (.invalidWordLiteral literal)
          | .integerLiteral _ _ =>
              failWith lift (.occurrence id.occurrence)
                (.requirementsPresent node.requirements)
          | .reference _ (.local binder) =>
              if scope.ids.contains binder then
                pure {
                  resolved := .var binder
                  consumedRequirements := []
                }
              else
                failWith lift (.occurrence id.occurrence)
                  (.unknownLocal binder)
          | .reference _ (.builtinBoolean value) => pure {
              resolved := .bool value
              consumedRequirements := []
            }
          | .reference _ (.declaration _) =>
              failWith lift (.occurrence id.occurrence)
                (.unsupportedExpression .declarationReference)
          | .reference _ (.builtinFunction _) =>
              failWith lift (.occurrence id.occurrence)
                (.unsupportedExpression .declarationReference)
          | .group inner => recurse inner
          | .tuple elements => do
              let lowered ← elements.mapM recurse
              pure {
                resolved := productExpression
                  (lowered.map fun element => element.resolved)
                consumedRequirements := lowered.flatMap
                  (fun element => element.consumedRequirements)
              }
          | .unary _ _ =>
              failWith lift (.occurrence id.occurrence)
                (.requirementsPresent node.requirements)
          | .binary _ _ _ =>
              failWith lift (.occurrence id.occurrence)
                (.requirementsPresent node.requirements)
          | .conditional condition thenBranch elseBranch => do
              let condition ← recurse condition
              let thenBranch ← recurse thenBranch
              let elseBranch ← recurse elseBranch
              pure {
                resolved := .ifE condition.resolved thenBranch.resolved
                  elseBranch.resolved
                consumedRequirements :=
                  condition.consumedRequirements ++
                  thenBranch.consumedRequirements ++
                  elseBranch.consumedRequirements
              }
          | .call _ _ _ =>
              failWith lift (.occurrence id.occurrence)
                (.unsupportedExpression .call)
          | .lambda _ _ _ => failWith lift (.occurrence id.occurrence)
              (.unsupportedExpression .lambda)
          | .constructor _ _ => failWith lift (.occurrence id.occurrence)
              (.unsupportedExpression .constructor)
          | .member _ _ _ => failWith lift (.occurrence id.occurrence)
              (.unsupportedExpression .member)
          | .proxy _ => failWith lift (.occurrence id.occurrence)
              (.unsupportedExpression .proxy)
          | .index _ _ => failWith lift (.occurrence id.occurrence)
              (.unsupportedExpression .index)

/-- Decide whether a compile-time-classified expression is closed relative to
the staged values currently known while building a reusable runtime draft.
Requirement-bearing unary and binary forms, plus nonempty coercion paths, are
eligible only through their dedicated staged policies and retain their exact
requirement checks.  Other evidence-bearing base forms remain on ordinary
lowering. -/
private def stagedValueCacheEligible
    (analysis : SourceStageAnalysis.Analysis) (source : TypedSource)
    (environment : StagedValueEnvironment) : Nat → ExpressionId → Bool
  | 0, _ => false
  | fuel + 1, id =>
      match analysis.expressionStage? id, source.lookupExpression? id with
      | some .comptime, some node =>
          let recurse := stagedValueCacheEligible analysis source environment fuel
          match node.form with
          | .integerLiteral _ _ => node.coercions.isEmpty
          | .call _ arguments (.declaration instantiation) =>
              instantiation.returnComptime && arguments.all recurse
          | .unary _ operand => recurse operand
          | .binary left _ right => recurse left && recurse right
          | form =>
              (node.requirements.isEmpty || !node.coercions.isEmpty) &&
                match form with
                | .literal _ => true
                | .reference _ (.local binder) => environment.contains binder
                | .reference _ (.builtinBoolean _) => true
                | .group inner => recurse inner
                | .tuple elements => elements.all recurse
                | .conditional condition thenBranch elseBranch =>
                    recurse condition && recurse thenBranch &&
                      recurse elseBranch
                | _ => false
      | _, _ => false

/-- Lower one expression by following category-safe occurrence edges.  Fuel is
derived from the finite node table and turns malformed cyclic tables into a
located error.  A nonempty coercion path is checked and planned once around a
coercion-cleared view of the base node. -/
private def lowerExpressionFuelWith {error : Type} (lift : Error → error)
    (onCall : StagedAwareCallElaborator error)
    (onStagedIntegerCall : StagedIntegerCallElaborator error)
    (stagedValuePolicy : Option (RawStagedValueLoweringPolicy error))
    (onRequiredUnary : RequiredUnaryElaborator error)
    (onRequiredBinary : RequiredBinaryElaborator error)
    (onCoercion : CoercionElaborator error)
    (solvedRequirements : List SolvedRequirement)
    (fuel : Nat) (source : TypedSource) (scope : Resolved.Context)
    (environment : StagedIntegerEnvironment)
    (stagedValueEnvironment : StagedValueEnvironment)
    (id : ExpressionId) :
    Except error LoweredExpression :=
  match fuel with
  | 0 => failWith lift (.occurrence id.occurrence) .expressionDepthLimit
  | fuel + 1 => do
      let node ← (lookupExpression source id).mapError lift
      let stagedValueArgument : StagedValueArgumentOracle error :=
        fun argument =>
          match stagedValuePolicy with
          | some policy =>
              if stagedValueCacheEligible policy.analysis source
                  stagedValueEnvironment (source.nodes.length + 1)
                  argument then
                return some
                  (← policy.evaluate stagedValueEnvironment argument).value
              else
                pure none
          | none => pure none
      let recurse := lowerExpressionFuelWith lift onCall onStagedIntegerCall
        stagedValuePolicy onRequiredUnary onRequiredBinary onCoercion
        solvedRequirements fuel source scope environment stagedValueEnvironment
      let lowerOrdinary :=
        match node.coercions with
        | [] =>
            lowerExpressionNodeWith lift onCall stagedValueArgument
              onRequiredUnary
              onRequiredBinary solvedRequirements source scope recurse node
        | first :: rest => do
            let prepared ← prepareCoercionPathWith lift node first rest
            let plans ← checkedCoercionPlansWith lift onCoercion scope node
              (first :: rest)
            let baseNode := {
              node with
              type := prepared.rawType
              requirements := prepared.remainingRequirements
              coercions := []
            }
            let base ← lowerExpressionNodeWith lift onCall
              stagedValueArgument onRequiredUnary
              onRequiredBinary solvedRequirements source scope recurse baseNode
            applyCoercionPlans base.resolved base.consumedRequirements plans
      match node.form with
      | .call _ _ (.declaration instantiation) =>
          match stagedValuePolicy with
          | some policy =>
              if instantiation.returnComptime &&
                  policy.analysis.expressionStage? id = some .comptime &&
                  stagedValueCacheEligible policy.analysis source
                    stagedValueEnvironment (source.nodes.length + 1) id then
                let evaluated ← policy.evaluate stagedValueEnvironment id
                pure {
                  resolved := SourceStagedValue.toResolved evaluated.value
                  consumedRequirements := evaluated.consumedRequirements
                }
              else
                lowerOrdinary
          | none => lowerOrdinary
      | .conditional _ _ _ =>
          -- Materialize an eligible conditional as one staged computation.
          -- Lowering its arms independently would invoke a staged call in a
          -- dynamically unselected arm before Core could choose the result.
          match stagedValuePolicy with
          | some policy =>
              if policy.analysis.expressionStage? id = some .comptime &&
                  stagedValueCacheEligible policy.analysis source
                    stagedValueEnvironment (source.nodes.length + 1) id then
                let evaluated ← policy.evaluate stagedValueEnvironment id
                pure {
                  resolved := SourceStagedValue.toResolved evaluated.value
                  consumedRequirements := evaluated.consumedRequirements
                }
              else
                lowerOrdinary
          | none => lowerOrdinary
      | .call callee arguments (.builtinFunction .wordFromInteger) =>
          lowerWordFromIntegerWith lift onStagedIntegerCall solvedRequirements
            source environment fuel node callee arguments
      | .call _ _ (.builtinFunction .integerEq) =>
          lowerStagedBoolWith lift onStagedIntegerCall solvedRequirements source
            environment (fuel + 1) id
      | .call _ _ (.builtinFunction .integerLt) =>
          lowerStagedBoolWith lift onStagedIntegerCall solvedRequirements source
            environment (fuel + 1) id
      | _ => lowerOrdinary

private def lowerExpressionAsWith {error : Type} (lift : Error → error)
    (onCall : StagedAwareCallElaborator error)
    (onStagedIntegerCall : StagedIntegerCallElaborator error)
    (stagedValuePolicy : Option (RawStagedValueLoweringPolicy error))
    (onRequiredUnary : RequiredUnaryElaborator error)
    (onRequiredBinary : RequiredBinaryElaborator error)
    (onCoercion : CoercionElaborator error)
    (solvedRequirements : List SolvedRequirement)
    (fuel : Nat) (source : TypedSource) (scope : Resolved.Context)
    (environment : StagedIntegerEnvironment)
    (stagedValueEnvironment : StagedValueEnvironment)
    (expected : Core.Ty) (id : ExpressionId) :
    Except error LoweredExpression := do
  let node ← (lookupExpression source id).mapError lift
  match node.form with
  | .call _ _ (.builtinFunction function) =>
      if node.type != function.returnType then
        failWith lift (.occurrence id.occurrence)
          (.builtinFunctionCallTypeMismatch function function.returnType
            node.type)
  | _ => pure ()
  ensureTypeWith lift (.occurrence id.occurrence) expected node.type
  lowerExpressionFuelWith lift onCall onStagedIntegerCall stagedValuePolicy
    onRequiredUnary onRequiredBinary onCoercion solvedRequirements fuel source
    scope environment stagedValueEnvironment id

private inductive MatchPatternLeaf where
  | wildcard
  | integerLiteral (literal : Syntax.CoreLiteral)
  | unsupported

private def matchPatternLeaf : MatchPatternSource → MatchPatternLeaf
  | .wildcard _ _ => .wildcard
  | .integerLiteral _ literal => .integerLiteral literal
  | .binder _ _ => .unsupported
  | .constructor _ _ _ _ _ => .unsupported
  | .group _ inner => matchPatternLeaf inner
  | .tuple _ _ => .unsupported

private structure LoweredMatchPattern where
  tag : Option Core.Word
  consumedRequirements : List RequirementId

private structure LoweredMatchCase where
  pattern : LoweredMatchPattern
  branch : LoweredExpression

private def lowerMatchPatternWith {error : Type} (lift : Error → error)
    (site : ErrorSite) (solvedRequirements : List SolvedRequirement)
    (scrutineeType : Ty) (pattern : TypedMatchPattern) :
    Except error LoweredMatchPattern := do
  if pattern.type != scrutineeType then
    failWith lift site
      (.matchPatternTypeMismatch scrutineeType pattern.type)
  else
    match matchPatternLeaf pattern.source, pattern.resolution with
    | .wildcard, .wildcard =>
        if pattern.requirements.isEmpty then
          pure { tag := none, consumedRequirements := [] }
        else
          failWith lift site
            (.matchPatternRequirementsMismatch [] pattern.requirements)
    | .integerLiteral literal, .integerLiteral source resolution =>
        if literal.value != source then
          failWith lift site .matchPatternSourceMismatch
        else
          let lowered ← lowerIntegerLiteralResolutionWith lift site
            solvedRequirements pattern.type pattern.requirements source
            resolution
          match lowered.resolved with
          | .word word => pure {
              tag := some word
              consumedRequirements := lowered.consumedRequirements
            }
          | _ => failWith lift site .matchPatternSourceMismatch
    | _, _ => failWith lift site .matchPatternSourceMismatch

private def foldLoweredMatchCases (hidden : Resolved.LocalId)
    (cases : List LoweredMatchCase) (fallback : Option Resolved.Expr) :
    Option Resolved.Expr :=
  cases.foldr (fun arm tail =>
    match arm.pattern.tag with
    | none => some arm.branch.resolved
    | some word => tail.map fun rest =>
        .ifE (.binary .wordEq (.var hidden) (.word word))
          arm.branch.resolved rest) fallback

private def statementRoots : List NodeId → Except Error (List StatementId)
  | [] => .ok []
  | .statement id :: rest => do
      pure (id :: (← statementRoots rest))
  | .expression id :: _ =>
      fail (.occurrence id.occurrence) .expectedStatementNode

private def finalStatement? : List StatementId → Option StatementId
  | [] => none
  | [id] => some id
  | _ :: rest => finalStatement? rest

/-- Lower the tail-normal statement profile.  Each statement edge consumes
fuel, while expression edges consume the remaining fuel independently. -/
private def lowerStatementsFuelWith {error : Type} (lift : Error → error)
    (onCall : StagedAwareCallElaborator error)
    (onStagedIntegerCall : StagedIntegerCallElaborator error)
    (stagedValuePolicy : Option (RawStagedValueLoweringPolicy error))
    (onRequiredUnary : RequiredUnaryElaborator error)
    (onRequiredBinary : RequiredBinaryElaborator error)
    (onCoercion : CoercionElaborator error)
    (solvedRequirements : List SolvedRequirement) :
    Nat → TypedSource → Resolved.Context → StagedIntegerEnvironment →
      StagedValueEnvironment → Core.Ty → ErrorSite → ErrorReason →
      List StatementId →
      Except error LoweredExpression
  | _, _, _, _, _, _, fallthroughSite, fallthroughReason, [] =>
      failWith lift fallthroughSite fallthroughReason
  | 0, _, _, _, _, _, _, _, id :: _ =>
      failWith lift (.occurrence id.occurrence) .statementDepthLimit
  | fuel + 1, source, scope, environment, stagedValueEnvironment, expected,
      fallthroughSite,
      fallthroughReason, id :: rest => do
    let node ← (lookupStatement source id).mapError lift
    let site := ErrorSite.occurrence id.occurrence
    match node.form with
    | .letDecl binder initializer => do
        ensureTypeWith lift site .unit node.type
        if scope.ids.contains binder.id || environment.contains binder.id then
          failWith lift (.binder binder.id) (.duplicateLocal binder.id)
        else if binder.scheme.quantified.isEmpty &&
            binder.scheme.body == Ty.integer then
          validateStagedIntegerBinderWith lift (.binder binder.id) source binder
          let initializer ← match initializer with
            | none => failWith lift site .uninitializedLet
            | some initializer =>
                evaluateStagedIntegerFuelWith lift onStagedIntegerCall
                  solvedRequirements source environment true fuel initializer
          let body ← lowerStatementsFuelWith lift onCall
            onStagedIntegerCall stagedValuePolicy onRequiredUnary
            onRequiredBinary onCoercion solvedRequirements fuel source scope
            ({ binder, value := initializer.value } :: environment)
            stagedValueEnvironment expected fallthroughSite fallthroughReason
            rest
          pure {
            resolved := body.resolved
            consumedRequirements := initializer.consumedRequirements ++
              body.consumedRequirements
          }
        else if !binder.scheme.quantified.isEmpty then
          failWith lift (.binder binder.id)
            (.polymorphicLocal binder.scheme.quantified)
        else
          let binderType ← (lowerType (.binder binder.id)
            binder.scheme.body).mapError lift
          let initializerId ← match initializer with
            | none => failWith lift site .uninitializedLet
            | some initializer => pure initializer
          let lowerOrdinary : Except error LoweredExpression := do
            let initializer ← lowerExpressionAsWith lift onCall
              onStagedIntegerCall stagedValuePolicy onRequiredUnary
              onRequiredBinary onCoercion solvedRequirements fuel source scope
              environment stagedValueEnvironment binderType initializerId
            let body ← lowerStatementsFuelWith lift onCall
              onStagedIntegerCall stagedValuePolicy onRequiredUnary
              onRequiredBinary onCoercion solvedRequirements fuel source
              ((binder.id, binderType) :: scope) environment
              stagedValueEnvironment expected fallthroughSite fallthroughReason
              rest
            pure {
              resolved := .letE binder.id initializer.resolved body.resolved
              consumedRequirements := initializer.consumedRequirements ++
                body.consumedRequirements
            }
          match stagedValuePolicy with
          | some policy =>
              if policy.analysis.binderStage? binder.id = some .comptime &&
                  policy.analysis.expressionStage? initializerId =
                    some .comptime &&
                  stagedValueCacheEligible policy.analysis source
                    stagedValueEnvironment (source.nodes.length + 1)
                    initializerId then
                if binder.id.owner != source.owner then
                  failWith lift (.binder binder.id)
                    (.ownerMismatch source.owner binder.id.owner)
                let evaluated ← policy.evaluate stagedValueEnvironment
                  initializerId
                let actualType :=
                  SourceStagedValue.sourceType evaluated.value
                if actualType != binder.scheme.body then
                  failWith lift (.binder binder.id)
                    (.stagedValueTypeMismatch binder.scheme.body actualType)
                let body ← lowerStatementsFuelWith lift onCall
                  onStagedIntegerCall stagedValuePolicy onRequiredUnary
                  onRequiredBinary onCoercion solvedRequirements fuel source
                  ((binder.id, binderType) :: scope) environment
                  ({ binder, value := evaluated.value } ::
                    stagedValueEnvironment)
                  expected fallthroughSite fallthroughReason rest
                pure {
                  resolved := .letE binder.id
                    (SourceStagedValue.toResolved evaluated.value)
                    body.resolved
                  consumedRequirements := evaluated.consumedRequirements ++
                    body.consumedRequirements
                }
              else
                lowerOrdinary
          | none => lowerOrdinary
    | .returnStmt value => do
        if !rest.isEmpty then
          failWith lift site (.nonTailStatement .returnStmt)
        else
          ensureTypeWith lift site expected node.type
          match value with
          | none =>
              if expected = .unit then
                pure {
                  resolved := .unit
                  consumedRequirements := []
                }
              else
                failWith lift site (.typedNodeTypeMismatch expected .unit)
          | some value =>
              lowerExpressionAsWith lift onCall onStagedIntegerCall
                stagedValuePolicy onRequiredUnary onRequiredBinary onCoercion
                solvedRequirements fuel source scope environment
                stagedValueEnvironment expected value
    | .ifThen condition thenBody elseBody => do
        if !rest.isEmpty then
          failWith lift site (.nonTailStatement .ifThen)
        else
          match elseBody with
          | none => failWith lift site .missingElseBranch
          | some elseBody => do
              ensureTypeWith lift site expected node.type
              let condition ← lowerExpressionAsWith lift onCall
                onStagedIntegerCall stagedValuePolicy onRequiredUnary
                onRequiredBinary onCoercion solvedRequirements fuel source scope
                environment stagedValueEnvironment .bool condition
              let thenBranch ← lowerStatementsFuelWith lift onCall
                onStagedIntegerCall stagedValuePolicy onRequiredUnary
                onRequiredBinary onCoercion solvedRequirements fuel source scope
                environment stagedValueEnvironment expected site
                (.conditionalBranchFallthrough .thenBranch) thenBody
              let elseBranch ← lowerStatementsFuelWith lift onCall
                onStagedIntegerCall stagedValuePolicy onRequiredUnary
                onRequiredBinary onCoercion solvedRequirements fuel source scope
                environment stagedValueEnvironment expected site
                (.conditionalBranchFallthrough .elseBranch) elseBody
              pure {
                resolved := .ifE condition.resolved thenBranch.resolved
                  elseBranch.resolved
                consumedRequirements := condition.consumedRequirements ++
                  thenBranch.consumedRequirements ++
                  elseBranch.consumedRequirements
              }
    | .block body => do
        if !rest.isEmpty then
          failWith lift site (.nonTailStatement .block)
        else
          ensureTypeWith lift site expected node.type
          lowerStatementsFuelWith lift onCall onStagedIntegerCall
            stagedValuePolicy onRequiredUnary onRequiredBinary onCoercion
            solvedRequirements fuel source scope environment
            stagedValueEnvironment expected site .blockFallthrough body
    | .matchWith resolution => do
        if !rest.isEmpty then
          failWith lift site (.nonTailStatement .matchWith)
        else if resolution.hiddenScrutinee.owner != source.owner then
          failWith lift site (.matchHiddenOwnerMismatch source.owner
            resolution.hiddenScrutinee.owner)
        else if scope.ids.contains resolution.hiddenScrutinee ||
            environment.contains resolution.hiddenScrutinee then
          failWith lift site (.duplicateMatchHidden
            resolution.hiddenScrutinee)
        else
          ensureTypeWith lift site expected node.type
          let scrutineeNode ←
            (lookupExpression source resolution.scrutinee).mapError lift
          let scrutineeCoreType ←
            (lowerType (.occurrence resolution.scrutinee.occurrence)
              scrutineeNode.type).mapError lift
          let scrutinee ← lowerExpressionAsWith lift onCall
            onStagedIntegerCall stagedValuePolicy onRequiredUnary
            onRequiredBinary onCoercion solvedRequirements fuel source scope
            environment stagedValueEnvironment scrutineeCoreType
            resolution.scrutinee
          let expectedRequirements := resolution.cases.flatMap fun arm =>
            arm.pattern.requirements
          if resolution.requirements != expectedRequirements then
            failWith lift site (.matchRequirementsMismatch
              expectedRequirements resolution.requirements)
          else
            let loweredCases ← resolution.cases.mapM fun arm => do
              let pattern ← lowerMatchPatternWith lift site solvedRequirements
                scrutineeNode.type arm.pattern
              let branch ← lowerStatementsFuelWith lift onCall
                onStagedIntegerCall stagedValuePolicy onRequiredUnary
                onRequiredBinary onCoercion solvedRequirements fuel source scope
                environment stagedValueEnvironment expected site
                .blockFallthrough arm.body
              pure { pattern, branch }
            let fallback ← match resolution.defaultBody with
              | none => pure none
              | some body => do
                  let lowered ← lowerStatementsFuelWith lift onCall
                    onStagedIntegerCall stagedValuePolicy onRequiredUnary
                    onRequiredBinary onCoercion solvedRequirements fuel source
                    scope environment stagedValueEnvironment expected site
                    .blockFallthrough body
                  pure (some lowered)
            let folded := foldLoweredMatchCases resolution.hiddenScrutinee
              loweredCases (fallback.map (·.resolved))
            let selected ← match folded with
              | some selected => pure selected
              | none => failWith lift site .matchWithoutFallback
            pure {
              resolved := .letE resolution.hiddenScrutinee
                scrutinee.resolved selected
              consumedRequirements :=
                scrutinee.consumedRequirements ++
                loweredCases.flatMap (fun arm =>
                  arm.pattern.consumedRequirements ++
                    arm.branch.consumedRequirements) ++
                fallback.toList.flatMap (·.consumedRequirements)
            }
    | .expression _ _ =>
        failWith lift site (.unsupportedStatement .expression)
    | .assignValue _ _ _
    | .assignBitNot _ =>
        failWith lift site (.unsupportedStatement .assignment)
    | .forLoop _ _ _ _
    | .whileLoop _ _ =>
        failWith lift site (.unsupportedStatement .loop)
    | .breakStmt
    | .continueStmt =>
        failWith lift site (.unsupportedStatement .loopControl)

private def bindStagedIntegerInputsWith {error : Type}
    (lift : Error → error) (source : TypedSource) :
    List Resolved.LocalId → List TypedBinder → List Int →
      Except error StagedIntegerEnvironment
  | _, [], [] => pure []
  | seen, binder :: rest, value :: values => do
      if binder.id.owner != source.owner then
        failWith lift (.binder binder.id)
          (.ownerMismatch source.owner binder.id.owner)
      else if seen.contains binder.id then
        failWith lift (.binder binder.id) (.duplicateInput binder.id)
      else if !binder.scheme.quantified.isEmpty then
        failWith lift (.binder binder.id)
          (.polymorphicInput binder.scheme.quantified)
      else if binder.scheme.body != Ty.integer then
        failWith lift (.binder binder.id)
          (.stagedIntegerTypeMismatch .integer binder.scheme.body)
      else
        pure ({ binder, value } ::
          (← bindStagedIntegerInputsWith lift source (binder.id :: seen)
            rest values))
  | _, binders, values =>
      failWith lift (.declaration source.owner)
        (.stagedIntegerArgumentArityMismatch binders.length values.length)

/-- Evaluate the pure tail-normal statement subset used by an integer-returning
staged function.  Integer lets are strict and erased.  Both arms of a terminal
conditional are validated and accounted in source order, but only the selected
arm may invoke a staged call. -/
private def evaluateStagedIntegerStatementsFuelWith {error : Type}
    (lift : Error → error)
    (onStagedIntegerCall : StagedIntegerCallElaborator error)
    (solvedRequirements : List SolvedRequirement) (execute : Bool) :
    Nat → TypedSource → StagedIntegerEnvironment → ErrorSite →
      ErrorReason → List StatementId →
      Except error StagedIntegerEvaluation
  | _, _, _, fallthroughSite, fallthroughReason, [] =>
      failWith lift fallthroughSite fallthroughReason
  | 0, _, _, _, _, id :: _ =>
      failWith lift (.occurrence id.occurrence) .statementDepthLimit
  | fuel + 1, source, environment, fallthroughSite, fallthroughReason,
      id :: rest => do
    let node ← (lookupStatement source id).mapError lift
    let site := ErrorSite.occurrence id.occurrence
    match node.form with
    | .letDecl binder initializer => do
        ensureTypeWith lift site .unit node.type
        if environment.contains binder.id then
          failWith lift (.binder binder.id) (.duplicateLocal binder.id)
        else
          validateStagedIntegerBinderWith lift (.binder binder.id) source binder
          let initializer ← match initializer with
            | none => failWith lift site .uninitializedLet
            | some initializer =>
                evaluateStagedIntegerFuelWith lift onStagedIntegerCall
                  solvedRequirements source environment execute fuel
                  initializer
          let body ← evaluateStagedIntegerStatementsFuelWith lift
            onStagedIntegerCall solvedRequirements execute fuel source
            ({ binder, value := initializer.value } :: environment)
            fallthroughSite fallthroughReason rest
          pure {
            value := body.value
            consumedRequirements := initializer.consumedRequirements ++
              body.consumedRequirements
          }
    | .returnStmt value => do
        if !rest.isEmpty then
          failWith lift site (.nonTailStatement .returnStmt)
        else if node.type != Ty.integer then
          failWith lift site (.stagedIntegerTypeMismatch .integer node.type)
        else
          match value with
          | none => failWith lift site .stagedIntegerStatementNotClosed
          | some value =>
              evaluateStagedIntegerFuelWith lift onStagedIntegerCall
                solvedRequirements source environment execute fuel value
    | .ifThen condition thenBody elseBody => do
        if !rest.isEmpty then
          failWith lift site (.nonTailStatement .ifThen)
        else if node.type != Ty.integer then
          failWith lift site (.stagedIntegerTypeMismatch .integer node.type)
        else
          match elseBody with
          | none => failWith lift site .missingElseBranch
          | some elseBody => do
              let condition ← evaluateStagedBoolFuelWith lift
                onStagedIntegerCall solvedRequirements source environment
                execute fuel condition
              let thenBranch ← evaluateStagedIntegerStatementsFuelWith lift
                onStagedIntegerCall solvedRequirements
                (execute && condition.value) fuel source environment
                site (.conditionalBranchFallthrough .thenBranch) thenBody
              let elseBranch ← evaluateStagedIntegerStatementsFuelWith lift
                onStagedIntegerCall solvedRequirements
                (execute && !condition.value) fuel source environment
                site (.conditionalBranchFallthrough .elseBranch) elseBody
              pure {
                value := if condition.value then thenBranch.value
                  else elseBranch.value
                consumedRequirements := condition.consumedRequirements ++
                  thenBranch.consumedRequirements ++
                  elseBranch.consumedRequirements
              }
    | .block body => do
        if !rest.isEmpty then
          failWith lift site (.nonTailStatement .block)
        else if node.type != Ty.integer then
          failWith lift site (.stagedIntegerTypeMismatch .integer node.type)
        else
          evaluateStagedIntegerStatementsFuelWith lift onStagedIntegerCall
            solvedRequirements execute fuel source environment site
            .blockFallthrough body
    | .matchWith _ =>
        failWith lift site .stagedIntegerStatementNotClosed
    | .expression _ _ =>
        failWith lift site (.unsupportedStatement .expression)
    | .assignValue _ _ _
    | .assignBitNot _ =>
        failWith lift site (.unsupportedStatement .assignment)
    | .forLoop _ _ _ _
    | .whileLoop _ _ =>
        failWith lift site (.unsupportedStatement .loop)
    | .breakStmt
    | .continueStmt =>
        failWith lift site (.unsupportedStatement .loopControl)

/-- Preserve the original call-free profile as a reusable call policy. -/
def rejectCalls : CallElaborator Error :=
  fun _ node _ _ _ =>
    if !node.requirements.isEmpty then
      fail (.occurrence node.id.occurrence)
        (.requirementsPresent node.requirements)
    else
      match lowerType (.occurrence node.id.occurrence) node.type with
      | .error error => .error error
      | .ok _ =>
          fail (.occurrence node.id.occurrence)
            (.unsupportedExpression .call)

/-- Preserve standalone closed staging by rejecting every ordinary source
function call.  Builtin integer intrinsics are intercepted before this policy. -/
def rejectStagedIntegerCalls : StagedIntegerCallElaborator Error :=
  rejectStagedIntegerCallsWith (fun error => error)

/-- Preserve the original evidence-free profile for requirement-bearing binary
expressions. -/
def rejectRequiredBinaries : RequiredBinaryElaborator Error :=
  fun _ node _ _ _ =>
    fail (.occurrence node.id.occurrence)
      (.requirementsPresent node.requirements)

/-- Preserve the original evidence-free profile for requirement-bearing unary
expressions. -/
def rejectRequiredUnaries : RequiredUnaryElaborator Error :=
  fun _ node _ _ =>
    fail (.occurrence node.id.occurrence)
      (.requirementsPresent node.requirements)

/-- Preserve the standalone profile's explicit coercion rejection while the
general policy entry point remains available to whole-program consumers. -/
def rejectCoercions : CoercionElaborator Error :=
  fun _ node _ =>
    fail (.occurrence node.id.occurrence)
      (.coercionsPresent node.coercions)

namespace Internal

/-- Internal proof interface to the existing expression traversal. This fixes
the standalone rejection policies and disables staged caching; it is not a
new expression compiler or a finalized public source API. -/
def lowerExpression (fuel : Nat) (source : TypedSource)
    (scope : Resolved.Context) (id : ExpressionId) :
    Except Error LoweredExpression :=
  lowerExpressionFuelWith (fun error => error) (fun _ => rejectCalls)
    rejectStagedIntegerCalls none rejectRequiredUnaries rejectRequiredBinaries
    rejectCoercions [] fuel source scope [] [] id

private theorem lookupExpression_of_found
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    (found : source.lookupExpression? id = some node) :
    lookupExpression source id = .ok node := by
  unfold TypedSource.lookupExpression? at found
  cases lookup : source.lookupNode? id.occurrence with
  | none => simp [lookup] at found
  | some selected =>
      cases selected with
      | statement => simp [lookup] at found
      | expression selected =>
          simp only [lookup, Option.some.injEq] at found
          subst selected
          simp [lookupExpression, lookup]

theorem lowerExpression_unit
    (fuel : Nat) (source : TypedSource) (scope : Resolved.Context)
    (id : ExpressionId) (node : ExpressionNode)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .tuple []) (typed : node.type = .unit)
    (requirements : node.requirements = []) (coercions : node.coercions = []) :
    lowerExpression (fuel + 1) source scope id =
      .ok { resolved := .unit, consumedRequirements := [] } := by
  have lookup := lookupExpression_of_found found
  simp [lowerExpression, lowerExpressionFuelWith, lookup, Except.mapError,
    bind, Except.bind, pure, Pure.pure, Except.pure, coercions, form,
    lowerExpressionNodeWith, requirements, typed, Ty.unit, lowerType, productExpression]

theorem lowerExpression_bool
    (fuel : Nat) (source : TypedSource) (scope : Resolved.Context)
    (id : ExpressionId) (node : ExpressionNode) (name : String) (value : Bool)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .reference name (.builtinBoolean value))
    (typed : node.type = .bool)
    (requirements : node.requirements = []) (coercions : node.coercions = []) :
    lowerExpression (fuel + 1) source scope id =
      .ok { resolved := .bool value, consumedRequirements := [] } := by
  have lookup := lookupExpression_of_found found
  simp [lowerExpression, lowerExpressionFuelWith, lookup, Except.mapError,
    bind, Except.bind, pure, Pure.pure, Except.pure, coercions, form,
    lowerExpressionNodeWith, requirements, typed, Ty.bool, lowerType]

theorem lowerExpression_word
    (fuel : Nat) (source : TypedSource) (scope : Resolved.Context)
    (id : ExpressionId) (node : ExpressionNode)
    (literal : Syntax.CoreLiteralValue) (value : Core.Word)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .literal literal) (typed : node.type = .word)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (meaning : WordLiteralDenotes ⟨node.span, literal⟩ value) :
    lowerExpression (fuel + 1) source scope id =
      .ok { resolved := .word value, consumedRequirements := [] } := by
  have lookup := lookupExpression_of_found found
  have decoded := interpretWordLiteral?_complete meaning
  simp [lowerExpression, lowerExpressionFuelWith, lookup, Except.mapError,
    bind, Except.bind, pure, Pure.pure, Except.pure, coercions, form,
    lowerExpressionNodeWith, requirements, typed, Ty.word, lowerType, decoded]

theorem lowerExpression_pair
    (fuel : Nat) (source : TypedSource) (scope : Resolved.Context)
    (id : ExpressionId) (node : ExpressionNode) (leftId rightId : ExpressionId)
    (leftType rightType : Ty) (leftCoreType rightCoreType : Core.Ty)
    (left right : LoweredExpression)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .tuple [leftId, rightId])
    (typed : node.type = .product leftType rightType)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (leftTypeLowered : lowerType (.occurrence node.id.occurrence) leftType =
      .ok leftCoreType)
    (rightTypeLowered : lowerType (.occurrence node.id.occurrence) rightType =
      .ok rightCoreType)
    (leftLowered : lowerExpression fuel source scope leftId = .ok left)
    (rightLowered : lowerExpression fuel source scope rightId = .ok right) :
    lowerExpression (fuel + 1) source scope id = .ok {
      resolved := .pair left.resolved right.resolved
      consumedRequirements := left.consumedRequirements ++ right.consumedRequirements
    } := by
  have lookup := lookupExpression_of_found found
  unfold lowerExpression at leftLowered rightLowered ⊢
  rw [lowerExpressionFuelWith]
  simp only [lookup, Except.mapError, bind, Except.bind, coercions, form]
  simp [lowerExpressionNodeWith, form, requirements, typed, lowerType,
    leftTypeLowered, rightTypeLowered, leftLowered, rightLowered,
    productExpression, bind, Except.bind, pure, Pure.pure, Except.pure]

end Internal

private def reconcileConsumedRequirementsAux
    (declaration : Resolved.DeclarationId) (seen available : List RequirementId) :
    List RequirementId → Except Error (List RequirementId)
  | [] => pure available
  | requirement :: rest =>
      if seen.contains requirement then
        fail (.declaration declaration)
          (.duplicateConsumedRequirement requirement)
      else
        match eraseRequirement? requirement available with
        | none =>
            fail (.declaration declaration)
              (.unknownConsumedRequirement requirement)
        | some remaining =>
            reconcileConsumedRequirementsAux declaration
              (requirement :: seen) remaining rest

/-- Remove every reported discharge exactly once from the canonical solved
requirement order.  Unknown and repeated reports are errors; the returned list
is the still-unconsumed canonical suffix/interleaving in its original order. -/
def reconcileConsumedRequirements
    (declaration : Resolved.DeclarationId)
    (solved consumed : List RequirementId) :
    Except Error (List RequirementId) :=
  reconcileConsumedRequirementsAux declaration [] solved consumed

private def requireStagedExpressionWith {error : Type}
    (lift : Error → error) (analysis : SourceStageAnalysis.Analysis)
    (id : ExpressionId) : Except error Unit :=
  match analysis.expressionStage? id with
  | none =>
      failWith lift (.occurrence id.occurrence)
        .stagedValueExpressionStageMissing
  | some .runtime =>
      failWith lift (.occurrence id.occurrence) .stagedValueExpressionRuntime
  | some .deferred =>
      failWith lift (.occurrence id.occurrence) .stagedValueExpressionDeferred
  | some .comptime => pure ()

private def requireStagedBinderWith {error : Type}
    (lift : Error → error) (analysis : SourceStageAnalysis.Analysis)
    (binder : Resolved.LocalId) : Except error Unit :=
  match analysis.binderStage? binder with
  | none => failWith lift (.binder binder) .stagedValueBinderStageMissing
  | some .runtime => failWith lift (.binder binder) .stagedValueBinderRuntime
  | some .deferred => failWith lift (.binder binder) .stagedValueBinderDeferred
  | some .comptime => pure ()

private def ensureStagedValueTypeWith {error : Type}
    (lift : Error → error) (site : ErrorSite) (expected : Ty)
    (value : SourceStagedValue.Value) : Except error Unit :=
  let actual := SourceStagedValue.sourceType value
  if actual = expected then
    pure ()
  else
    failWith lift site (.stagedValueTypeMismatch expected actual)

private def stagedBoolWith {error : Type} (lift : Error → error)
    (site : ErrorSite) (value : SourceStagedValue.Value) : Except error Bool :=
  match value with
  | .bool value => pure value
  | value => failWith lift site
      (.stagedValueTypeMismatch .bool (SourceStagedValue.sourceType value))

private abbrev stagedValueOfCore? := SourceStagedValue.ofCore?

private def stagedProductValue : List SourceStagedValue.Value →
    SourceStagedValue.Value
  | [] => .unit
  | [value] => value
  | value :: rest => .product value (stagedProductValue rest)

/-- Produce a type-correct inert value for validate-only traversal.  Such a
value can flow through local bindings and structural checks, but it is never
returned from an executing branch or supplied to a staged call/method. -/
private def stagedPlaceholderWith {error : Type} (lift : Error → error)
    (site : ErrorSite) : Ty → Except error SourceStagedValue.Value
  | .constructor (.builtin .unit) => pure .unit
  | .constructor (.builtin .bool) => pure (.bool false)
  | .constructor (.builtin .word) => pure (.word (Core.Word.ofNatModulo 0))
  | .product left right => do
      pure (.product (← stagedPlaceholderWith lift site left)
        (← stagedPlaceholderWith lift site right))
  | type => failWith lift site (.unsupportedType type)

private def stagedCoreBinary? : Syntax.BinaryOp → Option Core.BinaryOp
  | .multiply => some .wordMul
  | .divide => some .wordDiv
  | .modulo => some .wordMod
  | .add => some .wordAdd
  | .subtract => some .wordSub
  | .bitAnd => some .wordAnd
  | .bitXor => some .wordXor
  | .bitOr => some .wordOr
  | .greater => some .wordGt
  | .equal => some .wordEq
  | .less
  | .lessEqual
  | .greaterEqual
  | .notEqual
  | .logicalAnd
  | .logicalOr => none

private def applyStagedBinary (operator : Syntax.BinaryOp)
    (left right : SourceStagedValue.Value) : Option SourceStagedValue.Value :=
  match operator, left, right with
  | .less, .word left, .word right =>
      some (.bool (decide (left.val < right.val)))
  | .lessEqual, .word left, .word right =>
      some (.bool (decide (left.val ≤ right.val)))
  | .greaterEqual, .word left, .word right =>
      some (.bool (decide (left.val ≥ right.val)))
  | .notEqual, .word left, .word right =>
      some (.bool (decide (left != right)))
  | .logicalAnd, .bool left, .bool right => some (.bool (left && right))
  | .logicalOr, .bool left, .bool right => some (.bool (left || right))
  | operator, left, right => do
      let coreOperator ← stagedCoreBinary? operator
      let value ← coreOperator.apply
        (SourceStagedValue.toCore left) (SourceStagedValue.toCore right)
      stagedValueOfCore? value

private def validateStagedValueBinderShapeWith {error : Type}
    (lift : Error → error) (site : ErrorSite) (source : TypedSource)
    (binder : TypedBinder) : Except error Unit := do
  if binder.id.owner != source.owner then
    failWith lift site (.ownerMismatch source.owner binder.id.owner)
  else if !binder.scheme.quantified.isEmpty then
    failWith lift site (.polymorphicLocal binder.scheme.quantified)
  else
    pure ()

private def validateStagedValueBindingWith {error : Type}
    (lift : Error → error) (site : ErrorSite) (source : TypedSource)
    (binding : StagedValueBinding) : Except error Unit := do
  validateStagedValueBinderShapeWith lift site source binding.binder
  ensureStagedValueTypeWith lift site binding.binder.scheme.body binding.value

private def evaluateStagedValueListWith {error : Type}
    (evaluate : ExpressionId → Except error StagedValueEvaluation) :
    List ExpressionId → Except error (List StagedValueEvaluation)
  | [] => pure []
  | expression :: rest => do
      let value ← evaluate expression
      let values ← evaluateStagedValueListWith evaluate rest
      pure (value :: values)

/-- Traverse one staged-value node in execution or validation mode.  Validation
retains stage/type/evidence/ledger checks while substituting inert values for
calls, selected methods, coercions, and primitive operations. -/
private def evaluateStagedValueNodeWith {error : Type}
    (lift : Error → error)
    (onStagedValueCall : StagedValueCallElaborator error)
    (onStagedValueRequiredUnary : StagedValueRequiredUnaryElaborator error)
    (onStagedValueRequiredBinary : StagedValueRequiredBinaryElaborator error)
    (solvedRequirements : List SolvedRequirement) (source : TypedSource)
    (environment : StagedValueEnvironment)
    (execute : Bool)
    (recurse : Bool → ExpressionId → Except error StagedValueEvaluation)
    (node : ExpressionNode) : Except error StagedValueEvaluation := do
      let site := ErrorSite.occurrence node.id.occurrence
      match node.form with
      | .integerLiteral literal resolution => do
          if node.type != Ty.word then
            failWith lift site (.stagedValueTypeMismatch .word node.type)
          let validated ← validateIntegerLiteralResolutionWith lift site
            solvedRequirements node.type node.requirements literal resolution
            (.builtin .intWord)
            (fun target =>
              if target = Ty.word then pure ()
              else failWith lift site
                (.stagedValueTypeMismatch .word target))
          pure {
            value := .word (Core.Word.ofNatModulo validated.rawValue)
            consumedRequirements := validated.consumedRequirements
          }
      | .call callee arguments (.declaration instantiation) => do
          let plan ← onStagedValueCall node callee arguments instantiation
          if plan.consumedRequirements != node.requirements then
            failWith lift site
              (.stagedValueCallRequirementsMismatch node.requirements
                plan.consumedRequirements)
          else if plan.argumentTypes.length != arguments.length then
            failWith lift site
              (.stagedValueCallArgumentArityMismatch
                plan.argumentTypes.length arguments.length)
          else if plan.resultType != node.type then
            failWith lift site
              (.stagedValueCallResultTypeMismatch node.type plan.resultType)
          else
            let evaluatedArguments ←
              (plan.argumentTypes.zip arguments).mapM fun pair => do
                let argumentNode ←
                  (lookupExpression source pair.2).mapError lift
                if argumentNode.type != pair.1 then
                  failWith lift (.occurrence pair.2.occurrence)
                    (.stagedValueTypeMismatch pair.1 argumentNode.type)
                else
                  let evaluated ← recurse execute pair.2
                  ensureStagedValueTypeWith lift
                    (.occurrence pair.2.occurrence) pair.1 evaluated.value
                  pure evaluated
            let value ← if execute then
                plan.invoke
                  (evaluatedArguments.map fun argument => argument.value)
              else
                stagedPlaceholderWith lift site node.type
            ensureStagedValueTypeWith lift site plan.resultType value
            pure {
              value
              consumedRequirements := evaluatedArguments.flatMap
                (fun argument => argument.consumedRequirements) ++
                plan.consumedRequirements
            }
      | .unary operator operand => do
          if node.requirements.isEmpty then
            let evaluated ← recurse execute operand
            let value ← if execute then do
                let coreOperator := match operator with
                  | .logicalNot => Core.UnaryOp.boolNot
                  | .bitNot => Core.UnaryOp.wordNot
                let coreValue ← match coreOperator.apply
                    (SourceStagedValue.toCore evaluated.value) with
                  | some value => pure value
                  | none =>
                      let reason := ErrorReason.stagedValueInvalidUnaryOperand
                        operator (SourceStagedValue.sourceType evaluated.value)
                      failWith lift site reason
                match stagedValueOfCore? coreValue with
                | some value => pure value
                | none =>
                    let reason := ErrorReason.stagedValueInvalidUnaryOperand
                      operator (SourceStagedValue.sourceType evaluated.value)
                    failWith lift site reason
              else
                stagedPlaceholderWith lift site node.type
            ensureStagedValueTypeWith lift site node.type value
            pure {
              value
              consumedRequirements := evaluated.consumedRequirements
            }
          else
            let plan ← onStagedValueRequiredUnary node operator operand
            if plan.consumedRequirements != node.requirements then
              failWith lift site
                (.stagedValueUnaryRequirementsMismatch node.requirements
                  plan.consumedRequirements)
            let operandNode ← (lookupExpression source operand).mapError lift
            let operandType ←
              (lowerType (.occurrence operand.occurrence)
                operandNode.type).mapError lift
            if plan.operandType != operandType then
              failWith lift site
                (.stagedValueUnaryOperandTypeMismatch operandType
                  plan.operandType)
            let resultType ← (lowerType site node.type).mapError lift
            if plan.resultType != resultType then
              failWith lift site
                (.stagedValueUnaryResultTypeMismatch resultType
                  plan.resultType)
            let evaluated ← recurse execute operand
            ensureStagedValueTypeWith lift (.occurrence operand.occurrence)
              operandNode.type evaluated.value
            let actualOperandType := SourceStagedValue.coreType evaluated.value
            if actualOperandType != plan.operandType then
              failWith lift site
                (.stagedValueUnaryOperandTypeMismatch plan.operandType
                  actualOperandType)
            let value ← if execute then
                plan.invoke evaluated.value
              else
                stagedPlaceholderWith lift site node.type
            let actualResultType := SourceStagedValue.coreType value
            if actualResultType != plan.resultType then
              failWith lift site
                (.stagedValueUnaryResultTypeMismatch plan.resultType
                  actualResultType)
            ensureStagedValueTypeWith lift site node.type value
            pure {
              value
              consumedRequirements := evaluated.consumedRequirements ++
                plan.consumedRequirements
            }
      | .binary left operator right => do
          if node.requirements.isEmpty then
            let left ← recurse execute left
            let right ← recurse execute right
            let value ← if execute then
                match applyStagedBinary operator left.value right.value with
                | some value => pure value
                | none =>
                    let reason := ErrorReason.stagedValueInvalidBinaryOperands
                      operator (SourceStagedValue.sourceType left.value)
                      (SourceStagedValue.sourceType right.value)
                    failWith lift site reason
              else
                stagedPlaceholderWith lift site node.type
            ensureStagedValueTypeWith lift site node.type value
            pure {
              value
              consumedRequirements := left.consumedRequirements ++
                right.consumedRequirements
            }
          else
            let plan ← onStagedValueRequiredBinary node left operator right
            if plan.consumedRequirements != node.requirements then
              failWith lift site
                (.stagedValueBinaryRequirementsMismatch node.requirements
                  plan.consumedRequirements)
            let leftNode ← (lookupExpression source left).mapError lift
            let leftType ← (lowerType (.occurrence left.occurrence)
              leftNode.type).mapError lift
            if plan.leftType != leftType then
              failWith lift site
                (.stagedValueBinaryLeftTypeMismatch leftType plan.leftType)
            let rightNode ← (lookupExpression source right).mapError lift
            let rightType ← (lowerType (.occurrence right.occurrence)
              rightNode.type).mapError lift
            if plan.rightType != rightType then
              failWith lift site
                (.stagedValueBinaryRightTypeMismatch rightType plan.rightType)
            let resultType ← (lowerType site node.type).mapError lift
            if plan.resultType != resultType then
              failWith lift site
                (.stagedValueBinaryResultTypeMismatch resultType
                  plan.resultType)
            let evaluatedLeft ← recurse execute left
            ensureStagedValueTypeWith lift (.occurrence left.occurrence)
              leftNode.type evaluatedLeft.value
            let actualLeftType := SourceStagedValue.coreType evaluatedLeft.value
            if actualLeftType != plan.leftType then
              failWith lift site
                (.stagedValueBinaryLeftTypeMismatch plan.leftType
                  actualLeftType)
            let evaluatedRight ← recurse execute right
            ensureStagedValueTypeWith lift (.occurrence right.occurrence)
              rightNode.type evaluatedRight.value
            let actualRightType := SourceStagedValue.coreType evaluatedRight.value
            if actualRightType != plan.rightType then
              failWith lift site
                (.stagedValueBinaryRightTypeMismatch plan.rightType
                  actualRightType)
            let value ← if execute then
                plan.invoke evaluatedLeft.value evaluatedRight.value
              else
                stagedPlaceholderWith lift site node.type
            let actualResultType := SourceStagedValue.coreType value
            if actualResultType != plan.resultType then
              failWith lift site
                (.stagedValueBinaryResultTypeMismatch plan.resultType
                  actualResultType)
            ensureStagedValueTypeWith lift site node.type value
            pure {
              value
              consumedRequirements := evaluatedLeft.consumedRequirements ++
                evaluatedRight.consumedRequirements ++
                plan.consumedRequirements
            }
      | form => do
          unless node.requirements.isEmpty do
            failWith lift site (.requirementsPresent node.requirements)
          match form with
          | .literal literal => do
              if node.type != Ty.word then
                failWith lift site (.stagedValueTypeMismatch .word node.type)
              match interpretWordLiteral? ⟨node.span, literal⟩ with
              | some word => pure {
                  value := .word word
                  consumedRequirements := []
                }
              | none => failWith lift site (.invalidWordLiteral literal)
          | .reference name (.local binder) => do
              if binder.owner != source.owner then
                failWith lift site (.ownerMismatch source.owner binder.owner)
              let binding ← match environment.lookup? binder with
                | some binding => pure binding
                | none => failWith lift site (.unknownLocal binder)
              validateStagedValueBindingWith lift site source binding
              if name != binding.binder.name then
                failWith lift site
                  (.stagedValueLocalSpellingMismatch binder
                    binding.binder.name name)
              if node.type != binding.binder.scheme.body then
                failWith lift site
                  (.stagedValueTypeMismatch binding.binder.scheme.body
                    node.type)
              pure { value := binding.value, consumedRequirements := [] }
          | .reference name (.builtinBoolean value) => do
              if node.type != Ty.bool then
                failWith lift site (.stagedValueTypeMismatch .bool node.type)
              let expected := builtinBooleanSpelling value
              if name = expected then
                pure { value := .bool value, consumedRequirements := [] }
              else
                failWith lift site
                  (.builtinBooleanSpellingMismatch value expected name)
          | .reference _ (.declaration _) =>
              failWith lift site
                (.unsupportedExpression .declarationReference)
          | .reference _ (.builtinFunction _) =>
              failWith lift site
                (.unsupportedExpression .declarationReference)
          | .group inner => do
              let evaluated ← recurse execute inner
              ensureStagedValueTypeWith lift site node.type evaluated.value
              pure evaluated
          | .tuple elements => do
              let evaluated ← evaluateStagedValueListWith
                (recurse execute) elements
              let value := stagedProductValue
                (evaluated.map fun element => element.value)
              ensureStagedValueTypeWith lift site node.type value
              pure {
                value
                consumedRequirements := evaluated.flatMap fun element =>
                  element.consumedRequirements
              }
          | .unary _ _
          | .binary _ _ _ =>
              failWith lift site (.requirementsPresent node.requirements)
          | .conditional condition thenBranch elseBranch => do
              let condition ← recurse execute condition
              let conditionValue ← stagedBoolWith lift site condition.value
              let thenBranch ← recurse (execute && conditionValue)
                thenBranch
              let elseBranch ← recurse (execute && !conditionValue)
                elseBranch
              let selected := if conditionValue then thenBranch.value
                else elseBranch.value
              ensureStagedValueTypeWith lift site node.type thenBranch.value
              ensureStagedValueTypeWith lift site node.type elseBranch.value
              pure {
                value := selected
                consumedRequirements := condition.consumedRequirements ++
                  thenBranch.consumedRequirements ++
                  elseBranch.consumedRequirements
              }
          | .call _ _ _ =>
              failWith lift site (.unsupportedExpression .call)
          | .lambda _ _ _ =>
              failWith lift site (.unsupportedExpression .lambda)
          | .constructor _ _ =>
              failWith lift site (.unsupportedExpression .constructor)
          | .member _ _ _ =>
              failWith lift site (.unsupportedExpression .member)
          | .proxy _ => failWith lift site (.unsupportedExpression .proxy)
          | .index _ _ => failWith lift site (.unsupportedExpression .index)
          | .integerLiteral _ _ =>
              failWith lift site .stagedValueStatementNotClosed

private def evaluateStagedValueFuelWith {error : Type}
    (lift : Error → error)
    (onStagedValueCall : StagedValueCallElaborator error)
    (onStagedValueCoercion : StagedValueCoercionElaborator error)
    (onStagedValueRequiredUnary : StagedValueRequiredUnaryElaborator error)
    (onStagedValueRequiredBinary : StagedValueRequiredBinaryElaborator error)
    (analysis : SourceStageAnalysis.Analysis)
    (solvedRequirements : List SolvedRequirement) (source : TypedSource)
    (environment : StagedValueEnvironment) (execute : Bool) :
    Nat → ExpressionId → Except error StagedValueEvaluation
  | 0, id =>
      failWith lift (.occurrence id.occurrence) .stagedValueDepthLimit
  | fuel + 1, id => do
      requireStagedExpressionWith lift analysis id
      let node ← (lookupExpression source id).mapError lift
      let site := ErrorSite.occurrence id.occurrence
      let recurse := fun mode =>
        evaluateStagedValueFuelWith lift onStagedValueCall
          onStagedValueCoercion onStagedValueRequiredUnary
          onStagedValueRequiredBinary analysis solvedRequirements source
          environment mode fuel
      match node.coercions with
      | [] =>
          evaluateStagedValueNodeWith lift onStagedValueCall
            onStagedValueRequiredUnary onStagedValueRequiredBinary
            solvedRequirements source environment execute recurse node
      | first :: rest => do
          let prepared ← prepareCoercionPathWith lift node first rest
          let plans ← checkedStagedValueCoercionPlansWith lift
            onStagedValueCoercion node (first :: rest)
          let baseNode := {
            node with
            type := prepared.rawType
            requirements := prepared.remainingRequirements
            coercions := []
          }
          let base ← evaluateStagedValueNodeWith lift onStagedValueCall
            onStagedValueRequiredUnary onStagedValueRequiredBinary
            solvedRequirements source environment execute recurse baseNode
          let evaluated ← if execute then
              applyStagedValueCoercionPlansWith lift site base.value
                base.consumedRequirements plans
            else
              pure {
                value := ← stagedPlaceholderWith lift site node.type
                consumedRequirements := base.consumedRequirements ++
                  plans.flatMap fun checked =>
                    checked.plan.consumedRequirements
              }
          ensureStagedValueTypeWith lift site node.type evaluated.value
          pure evaluated

/-- Evaluate a closed, Core-representable expression only when ADR-0357 has
classified that exact occurrence as compile-time available. -/
def evaluateStagedValueWith {error : Type} (lift : Error → error)
    (analysis : SourceStageAnalysis.Analysis)
    (solvedRequirements : List SolvedRequirement) (source : TypedSource)
    (id : ExpressionId) : Except error StagedValueEvaluation :=
  evaluateStagedValueFuelWith lift (rejectStagedValueCallsWith lift)
    (rejectStagedValueCoercionsWith lift)
    (rejectStagedValueRequiredUnariesWith lift)
    (rejectStagedValueRequiredBinariesWith lift) analysis solvedRequirements
    source [] true (source.nodes.length + 1) id

/-- Evaluate one staged expression in a declaration-owned lexical environment
while delegating only direct source calls to a whole-program consumer. -/
private def evaluateStagedValueInEnvironmentWith {error : Type}
    (lift : Error → error)
    (onStagedValueCall : StagedValueCallElaborator error)
    (onStagedValueCoercion : StagedValueCoercionElaborator error)
    (onStagedValueRequiredUnary : StagedValueRequiredUnaryElaborator error)
    (onStagedValueRequiredBinary : StagedValueRequiredBinaryElaborator error)
    (analysis : SourceStageAnalysis.Analysis)
    (solvedRequirements : List SolvedRequirement) (source : TypedSource)
    (environment : StagedValueEnvironment) (id : ExpressionId) :
    Except error StagedValueEvaluation :=
  evaluateStagedValueFuelWith lift onStagedValueCall onStagedValueCoercion
    onStagedValueRequiredUnary onStagedValueRequiredBinary analysis
    solvedRequirements source environment true (source.nodes.length + 1) id

/-- Standalone closed staged-value evaluation. -/
def evaluateStagedValue (analysis : SourceStageAnalysis.Analysis)
    (solvedRequirements : List SolvedRequirement) (source : TypedSource)
    (id : ExpressionId) : Except Error StagedValueEvaluation :=
  evaluateStagedValueWith (fun error => error) analysis solvedRequirements
    source id

private def bindStagedValueInputsWith {error : Type}
    (lift : Error → error) (analysis : SourceStageAnalysis.Analysis)
    (source : TypedSource) :
    List Resolved.LocalId → List TypedBinder → List SourceStagedValue.Value →
      Except error StagedValueEnvironment
  | _, [], [] => pure []
  | seen, binder :: rest, value :: values => do
      if seen.contains binder.id then
        failWith lift (.binder binder.id) (.duplicateInput binder.id)
      validateStagedValueBinderShapeWith lift (.binder binder.id) source binder
      requireStagedBinderWith lift analysis binder.id
      ensureStagedValueTypeWith lift (.binder binder.id) binder.scheme.body value
      pure ({ binder, value } ::
        (← bindStagedValueInputsWith lift analysis source
          (binder.id :: seen) rest values))
  | _, binders, values =>
      failWith lift (.declaration source.owner)
        (.stagedValueArgumentArityMismatch binders.length values.length)

/-- Validate positional call-site knowledge and retain only concrete marked
inputs in the private staged environment.  `none` deliberately introduces no
binding, so expressions depending on an unavailable input cannot be folded. -/
private def bindKnownStagedValueInputsWith {error : Type}
    (lift : Error → error) (analysis : SourceStageAnalysis.Analysis)
    (source : TypedSource) :
    List Resolved.LocalId → List TypedBinder → KnownStagedValueInputs →
      Except error StagedValueEnvironment
  | _, [], [] => pure []
  | seen, binder :: rest, value :: values => do
      if seen.contains binder.id then
        failWith lift (.binder binder.id) (.duplicateInput binder.id)
      validateStagedValueBinderShapeWith lift (.binder binder.id) source binder
      let environment ← bindKnownStagedValueInputsWith lift analysis source
        (binder.id :: seen) rest values
      match value with
      | none => pure environment
      | some value =>
          requireStagedBinderWith lift analysis binder.id
          ensureStagedValueTypeWith lift (.binder binder.id)
            binder.scheme.body value
          pure ({ binder, value } :: environment)
  | _, binders, values =>
      failWith lift (.declaration source.owner)
        (.stagedValueArgumentArityMismatch binders.length values.length)

private def evaluateStagedValueStatementsFuelWith {error : Type}
    (lift : Error → error)
    (onStagedValueCall : StagedValueCallElaborator error)
    (onStagedValueCoercion : StagedValueCoercionElaborator error)
    (onStagedValueRequiredUnary : StagedValueRequiredUnaryElaborator error)
    (onStagedValueRequiredBinary : StagedValueRequiredBinaryElaborator error)
    (analysis : SourceStageAnalysis.Analysis)
    (solvedRequirements : List SolvedRequirement) (execute : Bool) :
    Nat → TypedSource → StagedValueEnvironment → ErrorSite → ErrorReason →
      List StatementId → Except error StagedValueEvaluation
  | _, _, _, fallthroughSite, fallthroughReason, [] =>
      failWith lift fallthroughSite fallthroughReason
  | 0, _, _, _, _, id :: _ =>
      failWith lift (.occurrence id.occurrence) .stagedValueDepthLimit
  | fuel + 1, source, environment, fallthroughSite, fallthroughReason,
      id :: rest => do
    let node ← (lookupStatement source id).mapError lift
    let site := ErrorSite.occurrence id.occurrence
    match node.form with
    | .letDecl binder initializer => do
        if node.type != Ty.unit then
          failWith lift site (.stagedValueTypeMismatch .unit node.type)
        if environment.contains binder.id then
          failWith lift (.binder binder.id) (.duplicateLocal binder.id)
        validateStagedValueBinderShapeWith lift (.binder binder.id) source binder
        requireStagedBinderWith lift analysis binder.id
        let initializer ← match initializer with
          | none => failWith lift site .uninitializedLet
          | some initializer =>
              evaluateStagedValueFuelWith lift onStagedValueCall
                onStagedValueCoercion onStagedValueRequiredUnary
                onStagedValueRequiredBinary analysis solvedRequirements
                source environment execute fuel initializer
        ensureStagedValueTypeWith lift (.binder binder.id)
          binder.scheme.body initializer.value
        let body ← evaluateStagedValueStatementsFuelWith lift
          onStagedValueCall onStagedValueCoercion
          onStagedValueRequiredUnary onStagedValueRequiredBinary analysis
          solvedRequirements execute fuel source
          ({ binder, value := initializer.value } :: environment)
          fallthroughSite fallthroughReason rest
        pure {
          value := body.value
          consumedRequirements := initializer.consumedRequirements ++
            body.consumedRequirements
        }
    | .returnStmt value => do
        if !rest.isEmpty then
          failWith lift site (.nonTailStatement .returnStmt)
        match value with
        | none =>
            if node.type = Ty.unit then
              pure { value := .unit, consumedRequirements := [] }
            else
              failWith lift site .stagedValueStatementNotClosed
        | some value => do
            let evaluated ← evaluateStagedValueFuelWith lift
              onStagedValueCall onStagedValueCoercion
              onStagedValueRequiredUnary onStagedValueRequiredBinary analysis
              solvedRequirements source environment execute fuel value
            ensureStagedValueTypeWith lift site node.type evaluated.value
            pure evaluated
    | .ifThen condition thenBody elseBody => do
        if !rest.isEmpty then
          failWith lift site (.nonTailStatement .ifThen)
        let elseBody ← match elseBody with
          | some body => pure body
          | none => failWith lift site .missingElseBranch
        let condition ← evaluateStagedValueFuelWith lift onStagedValueCall
          onStagedValueCoercion onStagedValueRequiredUnary
          onStagedValueRequiredBinary analysis solvedRequirements source
          environment execute fuel condition
        let conditionValue ← stagedBoolWith lift site condition.value
        let thenBranch ← evaluateStagedValueStatementsFuelWith lift
          onStagedValueCall onStagedValueCoercion
          onStagedValueRequiredUnary onStagedValueRequiredBinary analysis
          solvedRequirements (execute && conditionValue) fuel source
          environment site
          (.conditionalBranchFallthrough .thenBranch) thenBody
        let elseBranch ← evaluateStagedValueStatementsFuelWith lift
          onStagedValueCall onStagedValueCoercion
          onStagedValueRequiredUnary onStagedValueRequiredBinary analysis
          solvedRequirements (execute && !conditionValue) fuel source
          environment site
          (.conditionalBranchFallthrough .elseBranch) elseBody
        let selected := if conditionValue then thenBranch.value
          else elseBranch.value
        ensureStagedValueTypeWith lift site node.type thenBranch.value
        ensureStagedValueTypeWith lift site node.type elseBranch.value
        pure {
          value := selected
          consumedRequirements := condition.consumedRequirements ++
            thenBranch.consumedRequirements ++
            elseBranch.consumedRequirements
        }
    | .block body => do
        if !rest.isEmpty then
          failWith lift site (.nonTailStatement .block)
        let evaluated ← evaluateStagedValueStatementsFuelWith lift
          onStagedValueCall onStagedValueCoercion
          onStagedValueRequiredUnary onStagedValueRequiredBinary analysis
          solvedRequirements execute fuel source environment site
          .blockFallthrough body
        ensureStagedValueTypeWith lift site node.type evaluated.value
        pure evaluated
    | .matchWith _ => failWith lift site .stagedValueStatementNotClosed
    | .expression _ _ =>
        failWith lift site (.unsupportedStatement .expression)
    | .assignValue _ _ _
    | .assignBitNot _ =>
        failWith lift site (.unsupportedStatement .assignment)
    | .forLoop _ _ _ _
    | .whileLoop _ _ =>
        failWith lift site (.unsupportedStatement .loop)
    | .breakStmt
    | .continueStmt =>
        failWith lift site (.unsupportedStatement .loopControl)

/-- Execute the Core-representable staged subset of one exact source
specialization with an explicit whole-program direct-call policy.  Stable input
identities and the specialization-owned stage table are checked before
evaluation, and the function-local requirement ledger is reconciled exactly
once. -/
def evaluateStagedValueFunctionWithPolicies {error : Type}
    (lift : Error → error)
    (onStagedValueCall : StagedValueCallElaborator error)
    (onStagedValueCoercion : StagedValueCoercionElaborator error)
    (onStagedValueRequiredUnary : StagedValueRequiredUnaryElaborator error)
    (onStagedValueRequiredBinary : StagedValueRequiredBinaryElaborator error)
    (specialized : SourceSpecialization.SpecializedFunction)
    (arguments : List SourceStagedValue.Value) :
    Except error SourceStagedValue.Value := do
  let function := specialized.function
  let source := function.typedBody
  if source.owner != specialized.declaration then
    failWith lift (.declaration specialized.declaration)
      (.ownerMismatch specialized.declaration source.owner)
  else if function.declaration != specialized.declaration then
    failWith lift (.declaration specialized.declaration)
      (.ownerMismatch specialized.declaration function.declaration)
  else if specialized.key.declaration != specialized.declaration then
    failWith lift (.declaration specialized.declaration)
      (.stagedValueSpecializationKeyMismatch specialized.declaration
        specialized.key.declaration)
  else if specialized.key.arguments !=
      specialized.parameterSubstitution.map Prod.snd then
    failWith lift (.declaration specialized.declaration)
      (.stagedValueSpecializationArgumentsMismatch
        (specialized.parameterSubstitution.map Prod.snd)
        specialized.key.arguments)
  else if source.inputs.length != arguments.length then
    failWith lift (.declaration function.declaration)
      (.stagedValueArgumentArityMismatch source.inputs.length arguments.length)
  else
    let expectedAnalysis ← match SourceStageAnalysis.analyzeFunction function with
      | .ok analysis => pure analysis
      | .error error =>
          failWith lift (.declaration function.declaration)
            (.stagedValueAnalysisFailure error)
    if expectedAnalysis != specialized.stageAnalysis then
      failWith lift (.declaration function.declaration)
        (.stagedValueAnalysisMismatch expectedAnalysis
          specialized.stageAnalysis)
    let environment ← bindStagedValueInputsWith lift
      specialized.stageAnalysis source [] source.inputs arguments
    let expectedType := Ty.function
      (Ty.productMany (source.inputs.map fun binder => binder.scheme.body))
      function.inferredBodyType
    if function.type != expectedType then
      failWith lift (.declaration function.declaration)
        (.stagedValueFunctionTypeMismatch expectedType function.type)
    let roots ← (statementRoots source.roots).mapError lift
    let fallthroughSite := match finalStatement? roots with
      | some statement => ErrorSite.occurrence statement.occurrence
      | none => ErrorSite.declaration function.declaration
    let evaluated ← evaluateStagedValueStatementsFuelWith lift
      onStagedValueCall onStagedValueCoercion onStagedValueRequiredUnary
      onStagedValueRequiredBinary specialized.stageAnalysis
      function.solvedRequirements true (source.nodes.length + 1) source
      environment fallthroughSite .statementListFallthrough roots
    ensureStagedValueTypeWith lift
      (.declaration function.declaration) function.inferredBodyType
      evaluated.value
    let solvedRequirements :=
      function.solvedRequirements.map fun requirement => requirement.id
    if evaluated.consumedRequirements != solvedRequirements then
      failWith lift (.declaration function.declaration)
        (.stagedValueRequirementsMismatch solvedRequirements
          evaluated.consumedRequirements)
    let unconsumed ← (reconcileConsumedRequirements function.declaration
      solvedRequirements evaluated.consumedRequirements).mapError lift
    unless unconsumed.isEmpty do
      failWith lift (.declaration function.declaration)
        (.unconsumedRequirements unconsumed)
    pure evaluated.value

/-- Compatibility entry point retaining explicit staged-coercion rejection. -/
def evaluateStagedValueFunctionWith {error : Type}
    (lift : Error → error)
    (onStagedValueCall : StagedValueCallElaborator error)
    (specialized : SourceSpecialization.SpecializedFunction)
    (arguments : List SourceStagedValue.Value) :
    Except error SourceStagedValue.Value :=
  evaluateStagedValueFunctionWithPolicies lift onStagedValueCall
    (rejectStagedValueCoercionsWith lift)
    (rejectStagedValueRequiredUnariesWith lift)
    (rejectStagedValueRequiredBinariesWith lift) specialized arguments

/-- Standalone staged-value execution retains the closed-call boundary. -/
def evaluateStagedValueFunction
    (specialized : SourceSpecialization.SpecializedFunction)
    (arguments : List SourceStagedValue.Value) :
    Except Error SourceStagedValue.Value :=
  evaluateStagedValueFunctionWith (fun error => error)
    (rejectStagedValueCallsWith (fun error => error)) specialized arguments

/-- Execute one checked integer-returning function in the closed staged domain.
Inputs are paired internally with the declaration-owned typed binders, so a
whole-program caller supplies only signed values and cannot forge the lexical
environment.  Callee requirements are reconciled here and never escape into a
caller's function-local ledger. -/
def evaluateStagedIntegerFunctionWith {error : Type}
    (lift : Error → error)
    (onStagedIntegerCall : StagedIntegerCallElaborator error)
    (function : CheckedFunction) (arguments : List Int) : Except error Int := do
  let source := function.typedBody
  if source.owner != function.declaration then
    failWith lift (.declaration function.declaration)
      (.ownerMismatch function.declaration source.owner)
  else if source.inputs.length != arguments.length then
    failWith lift (.declaration function.declaration)
      (.stagedIntegerArgumentArityMismatch source.inputs.length
        arguments.length)
  else
    let environment ← bindStagedIntegerInputsWith lift source []
      source.inputs arguments
    if function.inferredBodyType != Ty.integer then
      failWith lift (.declaration function.declaration)
        (.stagedIntegerTypeMismatch .integer function.inferredBodyType)
    let expectedType := Ty.function
      (Ty.productMany (source.inputs.map fun binder => binder.scheme.body))
      Ty.integer
    if function.type != expectedType then
      failWith lift (.declaration function.declaration)
        (.stagedIntegerFunctionTypeMismatch expectedType function.type)
    let roots ← (statementRoots source.roots).mapError lift
    let fallthroughSite := match finalStatement? roots with
      | some statement => ErrorSite.occurrence statement.occurrence
      | none => ErrorSite.declaration function.declaration
    let evaluated ← evaluateStagedIntegerStatementsFuelWith lift
      onStagedIntegerCall function.solvedRequirements true
      (source.nodes.length + 1) source environment fallthroughSite
      .statementListFallthrough roots
    let solvedRequirements :=
      function.solvedRequirements.map fun requirement => requirement.id
    let unconsumed ←
      (reconcileConsumedRequirements function.declaration solvedRequirements
        evaluated.consumedRequirements).mapError lift
    unless unconsumed.isEmpty do
      failWith lift (.declaration function.declaration)
        (.unconsumedRequirements unconsumed)
    pure evaluated.value

/-- Standalone staged-function execution retains the closed-call boundary. -/
def evaluateStagedIntegerFunction (function : CheckedFunction)
    (arguments : List Int) : Except Error Int :=
  evaluateStagedIntegerFunctionWith (fun error => error)
    rejectStagedIntegerCalls function arguments

private def lowerFunctionBodyWithRawStagedValuePolicy {error : Type}
    (lift : Error → error)
    (onCall : StagedAwareCallElaborator error)
    (onStagedIntegerCall : StagedIntegerCallElaborator error)
    (stagedValuePolicy : Option (RawStagedValueLoweringPolicy error))
    (onRequiredUnary : RequiredUnaryElaborator error)
    (onRequiredBinary : RequiredBinaryElaborator error)
    (onCoercion : CoercionElaborator error)
    (initialStagedValueEnvironment : StagedValueEnvironment)
    (function : CheckedFunction) :
    Except error BodyDraft := do
  let source := function.typedBody
  if source.owner != function.declaration then
    failWith lift (.declaration function.declaration)
      (.ownerMismatch function.declaration source.owner)
  else
    let roots ← (statementRoots source.roots).mapError lift
    let rootOccurrence ← match roots with
      | [] =>
          failWith lift (.declaration function.declaration)
            .statementListFallthrough
      | root :: _ => pure root.occurrence
    let inputs ← (lowerInputs source.inputs).mapError lift
    let expected ← (lowerType (.declaration function.declaration)
      function.inferredBodyType).mapError lift
    let fallthroughSite := match finalStatement? roots with
      | some statement => ErrorSite.occurrence statement.occurrence
      | none => ErrorSite.declaration function.declaration
    let lowered ← lowerStatementsFuelWith lift onCall onStagedIntegerCall
      stagedValuePolicy onRequiredUnary onRequiredBinary onCoercion
      function.solvedRequirements (source.nodes.length + 1) source inputs []
      initialStagedValueEnvironment expected fallthroughSite
      .statementListFallthrough roots
    let solvedRequirements :=
      function.solvedRequirements.map fun requirement => requirement.id
    let unconsumedRequirements ←
      (reconcileConsumedRequirements function.declaration solvedRequirements
        lowered.consumedRequirements).mapError lift
    pure {
      declaration := function.declaration
      inputs
      resolved := lowered.resolved
      returnType := expected
      rootOccurrence
      unconsumedRequirements
    }

/-- Lower a checked function body while separately delegating runtime calls and
closed staged-integer calls.  Both policies receive only their own fixed
builders; Source Core retains every recursive traversal and requirement gate. -/
def lowerFunctionBodyWithRuntimeAndStagedPolicies {error : Type}
    (lift : Error → error)
    (onCall : CallElaborator error)
    (onStagedIntegerCall : StagedIntegerCallElaborator error)
    (onRequiredUnary : RequiredUnaryElaborator error)
    (onRequiredBinary : RequiredBinaryElaborator error)
    (onCoercion : CoercionElaborator error)
    (function : CheckedFunction) :
    Except error BodyDraft :=
  lowerFunctionBodyWithRawStagedValuePolicy lift (fun _ => onCall)
    onStagedIntegerCall none onRequiredUnary onRequiredBinary onCoercion []
    function

/-- Lower one exact, call-site-specific specialization while exposing only a
read-only staged argument oracle to runtime-call planning.  Known marked input
values seed the private lexical staged environment; Core inputs and ordinary
argument lowering remain unchanged. -/
def lowerSpecializedFunctionBodyWithKnownStagedInputsAndRuntimePolicies
    {error : Type} (lift : Error → error)
    (onCall : StagedAwareCallElaborator error)
    (onStagedIntegerCall : StagedIntegerCallElaborator error)
    (stagedValuePolicy : StagedValueLoweringPolicy error)
    (onRequiredUnary : RequiredUnaryElaborator error)
    (onRequiredBinary : RequiredBinaryElaborator error)
    (onCoercion : CoercionElaborator error)
    (knownInputs : KnownStagedValueInputs)
    (specialized : SourceSpecialization.SpecializedFunction) :
    Except error BodyDraft := do
  let function := specialized.function
  let source := function.typedBody
  if source.owner != specialized.declaration then
    failWith lift (.declaration specialized.declaration)
      (.ownerMismatch specialized.declaration source.owner)
  else if function.declaration != specialized.declaration then
    failWith lift (.declaration specialized.declaration)
      (.ownerMismatch specialized.declaration function.declaration)
  else if specialized.key.declaration != specialized.declaration then
    failWith lift (.declaration specialized.declaration)
      (.stagedValueSpecializationKeyMismatch specialized.declaration
        specialized.key.declaration)
  else if specialized.key.arguments !=
      specialized.parameterSubstitution.map Prod.snd then
    failWith lift (.declaration specialized.declaration)
      (.stagedValueSpecializationArgumentsMismatch
        (specialized.parameterSubstitution.map Prod.snd)
        specialized.key.arguments)
  else
    let expectedAnalysis ← match SourceStageAnalysis.analyzeFunction function with
      | .ok analysis => pure analysis
      | .error error =>
          failWith lift (.declaration function.declaration)
            (.stagedValueAnalysisFailure error)
    if expectedAnalysis != specialized.stageAnalysis then
      failWith lift (.declaration function.declaration)
        (.stagedValueAnalysisMismatch expectedAnalysis
          specialized.stageAnalysis)
    if stagedValuePolicy.analysis != specialized.stageAnalysis then
      failWith lift (.declaration function.declaration)
        (.stagedValueAnalysisMismatch specialized.stageAnalysis
          stagedValuePolicy.analysis)
    let initialStagedValueEnvironment ← bindKnownStagedValueInputsWith lift
      specialized.stageAnalysis source [] source.inputs knownInputs
    let rawPolicy := some {
      analysis := specialized.stageAnalysis
      evaluate := fun environment id =>
        evaluateStagedValueInEnvironmentWith lift
          stagedValuePolicy.onStagedValueCall
          stagedValuePolicy.onStagedValueCoercion
          stagedValuePolicy.onStagedValueRequiredUnary
          stagedValuePolicy.onStagedValueRequiredBinary
          specialized.stageAnalysis function.solvedRequirements source
          environment id
    }
    lowerFunctionBodyWithRawStagedValuePolicy lift onCall
      onStagedIntegerCall rawPolicy onRequiredUnary onRequiredBinary onCoercion
      initialStagedValueEnvironment function

/-- Compatibility wrapper for a reusable runtime draft with no concrete input
knowledge.  Input-independent staged calls and closed lets may still
materialize, while an unavailable input introduces no staged binding. -/
def lowerSpecializedFunctionBodyWithRuntimeAndStagedPolicies
    {error : Type} (lift : Error → error)
    (onCall : CallElaborator error)
    (onStagedIntegerCall : StagedIntegerCallElaborator error)
    (stagedValuePolicy : StagedValueLoweringPolicy error)
    (onRequiredUnary : RequiredUnaryElaborator error)
    (onRequiredBinary : RequiredBinaryElaborator error)
    (onCoercion : CoercionElaborator error)
    (specialized : SourceSpecialization.SpecializedFunction) :
    Except error BodyDraft :=
  lowerSpecializedFunctionBodyWithKnownStagedInputsAndRuntimePolicies lift
    (fun _ => onCall) onStagedIntegerCall stagedValuePolicy onRequiredUnary
    onRequiredBinary onCoercion
    (specialized.function.typedBody.inputs.map fun _ => none) specialized

/-- Compatibility wrapper retaining the previous closed staged-call boundary
while exposing the established runtime call/evidence/coercion policies. -/
def lowerFunctionBodyWithRuntimePolicies {error : Type} (lift : Error → error)
    (onCall : CallElaborator error)
    (onRequiredUnary : RequiredUnaryElaborator error)
    (onRequiredBinary : RequiredBinaryElaborator error)
    (onCoercion : CoercionElaborator error)
    (function : CheckedFunction) :
    Except error BodyDraft :=
  lowerFunctionBodyWithRuntimeAndStagedPolicies lift onCall
    (rejectStagedIntegerCallsWith lift) onRequiredUnary onRequiredBinary
    onCoercion function

/-- Compatibility entry point for call, required-binary, and coercion
consumers.  Requirement-bearing unary expressions retain their former explicit
rejection until a consumer opts into `lowerFunctionBodyWithRuntimePolicies`. -/
def lowerFunctionBodyWithAllPolicies {error : Type} (lift : Error → error)
    (onCall : CallElaborator error)
    (onRequiredBinary : RequiredBinaryElaborator error)
    (onCoercion : CoercionElaborator error)
    (function : CheckedFunction) :
    Except error BodyDraft :=
  lowerFunctionBodyWithRuntimePolicies lift onCall
    (fun _ node _ _ =>
      failWith lift (.occurrence node.id.occurrence)
        (.requirementsPresent node.requirements))
    onRequiredBinary onCoercion function

/-- Compatibility entry point for call and required-binary consumers.  It
retains the previous explicit coercion rejection until a consumer opts into
`lowerFunctionBodyWithAllPolicies`. -/
def lowerFunctionBodyWithPolicies {error : Type} (lift : Error → error)
    (onCall : CallElaborator error)
    (onRequiredBinary : RequiredBinaryElaborator error)
    (function : CheckedFunction) :
    Except error BodyDraft :=
  lowerFunctionBodyWithAllPolicies lift onCall onRequiredBinary
    (fun _ node _ =>
      failWith lift (.occurrence node.id.occurrence)
        (.coercionsPresent node.coercions))
    function

/-- Compatibility entry point for call-aware consumers.  Requirement-bearing
binary expressions retain the original explicit rejection until the consumer
opts into `lowerFunctionBodyWithPolicies`. -/
def lowerFunctionBodyWith {error : Type} (lift : Error → error)
    (onCall : CallElaborator error) (function : CheckedFunction) :
    Except error BodyDraft :=
  lowerFunctionBodyWithPolicies lift onCall
    (fun _ node _ _ _ =>
      failWith lift (.occurrence node.id.occurrence)
        (.requirementsPresent node.requirements))
    function

/-- Finish a body draft through the unchanged evidence gate, exact positional
lowering and independent Core type reconstruction. -/
def BodyDraft.finalize (draft : BodyDraft) : Except Error ElaboratedFunction := do
    unless draft.unconsumedRequirements.isEmpty do
      throw {
        site := .declaration draft.declaration
        reason := .unconsumedRequirements
          draft.unconsumedRequirements
      }
    match lowered : draft.resolved.lower? draft.inputs.ids with
    | none => fail (.occurrence draft.rootOccurrence) .resolvedLoweringFailed
    | some core =>
        match inferred : Core.infer? draft.inputs.values core with
        | none => fail (.occurrence draft.rootOccurrence) .coreInferenceFailed
        | some actual =>
            if equal : actual = draft.returnType then
              pure {
                declaration := draft.declaration
                inputs := draft.inputs
                resolved := draft.resolved
                core
                returnType := draft.returnType
                resolvedLowered := lowered
                coreTypeChecked := by simpa [equal] using inferred
              }
            else
              fail (.occurrence draft.rootOccurrence)
                (.returnTypeMismatch draft.returnType actual)

/-- Lift finalization failures into a whole-program consumer's error type. -/
def BodyDraft.finalizeWith {error : Type} (lift : Error → error)
    (draft : BodyDraft) : Except error ElaboratedFunction :=
  draft.finalize.mapError lift

/-- Build the original call-rejecting body draft. -/
def lowerFunctionBody (function : CheckedFunction) : Except Error BodyDraft :=
  lowerFunctionBodyWith id rejectCalls function

/-- Lower a checked monomorphic builtin function body to the existing resolved
local fragment and then to an open, independently rechecked Core expression.
This compatibility entry point keeps rejecting every call. -/
def elaborateFunction (function : CheckedFunction) :
    Except Error ElaboratedFunction := do
  (← lowerFunctionBody function).finalize

end Solcore.Frontend.SourceCoreElaboration

/-!
## Consolidated module: `Solcore.Frontend.SourceCoreElaborationProperties`
-/

/-! Checked laws for the typed-source-to-Core elaboration boundary. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreElaboration

open SourceInference TypeSystem

@[simp] theorem lowerType_unit (site : ErrorSite) :
    lowerType site .unit = .ok .unit := by
  rfl

@[simp] theorem lowerType_bool (site : ErrorSite) :
    lowerType site .bool = .ok .bool := by
  rfl

@[simp] theorem lowerType_word (site : ErrorSite) :
    lowerType site .word = .ok .word := by
  rfl

theorem lowerType_product {site : ErrorSite} {left right : Ty}
    {loweredLeft loweredRight : Core.Ty}
    (leftAccepted : lowerType site left = .ok loweredLeft)
    (rightAccepted : lowerType site right = .ok loweredRight) :
    lowerType site (.product left right) =
      .ok (.product loweredLeft loweredRight) := by
  simp [lowerType, leftAccepted, rightAccepted, bind, Except.bind,
    pure, Pure.pure, Except.pure]

@[simp] theorem reconcileConsumedRequirements_nil
    (declaration : Resolved.DeclarationId) (solved : List RequirementId) :
    reconcileConsumedRequirements declaration solved [] = .ok solved := by
  rfl

@[simp] theorem reconcileConsumedRequirements_single
    (declaration : Resolved.DeclarationId) :
    reconcileConsumedRequirements declaration [⟨0⟩] [⟨0⟩] =
      .ok [] := by
  rfl

@[simp] theorem reconcileConsumedRequirements_unknown
    (declaration : Resolved.DeclarationId) (requirement : RequirementId) :
    reconcileConsumedRequirements declaration [] [requirement] =
      .error {
        site := .declaration declaration
        reason := .unknownConsumedRequirement requirement
      } := by
  rfl

@[simp] theorem reconcileConsumedRequirements_duplicate
    (declaration : Resolved.DeclarationId) :
    reconcileConsumedRequirements declaration [⟨0⟩] [⟨0⟩, ⟨0⟩] =
      .error {
        site := .declaration declaration
        reason := .duplicateConsumedRequirement ⟨0⟩
      } := by
  rfl

/-- Every successful source elaboration carries the independently checked Core
typing equation at its public boundary. -/
@[simp] theorem ElaboratedFunction.resolved_lowers
    (function : ElaboratedFunction) :
    function.resolved.lower? function.inputs.ids = some function.core :=
  function.resolvedLowered

@[simp] theorem ElaboratedFunction.core_infers
    (function : ElaboratedFunction) :
    Core.infer? function.inputs.values function.core =
      some function.returnType :=
  function.coreTypeChecked

end Solcore.Frontend.SourceCoreElaboration

namespace Solcore.Frontend.SourceCoreElaboration
open SourceInference TypeSystem

private theorem lowerType_word_source {site : ErrorSite} {type : Ty}
    (lowered : lowerType site type = .ok .word) : type = .word := by
  cases type with
  | «variable» | parameter | function | mapping | proxy | comptime | error =>
      simp [lowerType, fail] at lowered
  | constructor constructor =>
      cases constructor with
      | declaration => simp [lowerType, fail] at lowered
      | builtin builtin => cases builtin <;> simp_all [lowerType, fail, Ty.word]
  | product left right =>
      cases leftResult : lowerType site left <;>
        cases rightResult : lowerType site right <;>
          simp_all [lowerType, bind, Except.bind, pure, Pure.pure, Except.pure]
  | application function argument =>
      simp only [lowerType] at lowered
      split at lowered <;> simp [fail] at lowered

local instance : LawfulBEq RequirementId where
  rfl := by intro value; change (value.index == value.index) = true; simp
  eq_of_beq := by
    intro left right equal
    change (left.index == right.index) = true at equal
    have indices : left.index = right.index := beq_iff_eq.mp equal
    cases left
    cases right
    cases indices
    rfl

private theorem builtinWordPredicate_of_beq {predicate : ProgramPredicate}
    (equal : (predicate == ProgramSignatures.builtinIntPredicate .word) = true) :
    predicate = ProgramSignatures.builtinIntPredicate .word := by
  cases predicate with
  | mk trait subject arguments =>
    cases trait with
    | builtin builtin =>
      cases builtin
      change ((subject == .word) && (arguments == [])) = true at equal
      simp only [Bool.and_eq_true, beq_iff_eq] at equal
      rcases equal with ⟨rfl, rfl⟩
      rfl
    | declaration id =>
      change false = true at equal
      contradiction

private theorem exactIntegerLiteralRequirementWith_member
    {site : ErrorSite} {requirements : List SolvedRequirement}
    {requirement : RequirementId} {solved : SolvedRequirement}
    (found : exactIntegerLiteralRequirementWith id site requirements requirement = .ok solved) :
    solved ∈ requirements ∧ solved.id = requirement := by
  unfold exactIntegerLiteralRequirementWith at found
  dsimp only at found
  split at found
  · simp [failWith] at found
  · rename_i selected exact
    simp only [pure, Pure.pure, Except.pure, Except.ok.injEq] at found
    subst solved
    have member : selected ∈ requirements.filter (fun item => decide (item.id = requirement)) := by
      rw [exact]
      simp
    simpa using member
  · simp [failWith] at found

/-- Facts established by successful Word-literal validation. The evidence entry
is taken from the supplied ledger; this certificate does not assume that the
entire ledger is semantically valid. -/
structure WordIntegerLiteralCertificate
    (solvedRequirements : List SolvedRequirement) (node : ExpressionNode)
    (source : Syntax.CoreLiteralValue) (resolution : IntegerLiteralResolution)
    (validated : WordIntegerLiteral) : Prop where
  targetType : resolution.targetType = .word
  nodeType : node.type = .word
  requirements : node.requirements = [resolution.requirement]
  coercions : node.coercions = []
  meaning : NumericLiteralDenotes source resolution.rawValue
  value : validated.value = Core.Word.ofNatModulo resolution.rawValue
  consumedRequirements : validated.consumedRequirements = [resolution.requirement]
  solved : ∃ solved ∈ solvedRequirements, solved.id = resolution.requirement ∧
    solved.predicate = ProgramSignatures.builtinIntPredicate .word

/-- Extract the literal's static semantic facts from the actual validator. No
evaluation derivation or successful lowering is assumed. -/
theorem validateWordIntegerLiteral_sound
    {solvedRequirements : List SolvedRequirement} {node : ExpressionNode}
    {source : Syntax.CoreLiteralValue} {resolution : IntegerLiteralResolution}
    {validated : WordIntegerLiteral}
    (accepted : validateWordIntegerLiteral solvedRequirements node source resolution = .ok validated) :
    WordIntegerLiteralCertificate solvedRequirements node source resolution validated := by
  have emptyCoercions : node.coercions = [] := by
    by_cases empty : node.coercions = []
    · exact empty
    · simp [validateWordIntegerLiteral, empty, fail, bind, Except.bind] at accepted
  simp only [validateWordIntegerLiteral, emptyCoercions, List.isEmpty_nil, ↓reduceIte] at accepted
  unfold validateWordIntegerLiteralWith at accepted
  cases checked : validateIntegerLiteralResolutionWith id (.occurrence node.id.occurrence)
      solvedRequirements node.type node.requirements source resolution (.builtin .intWord)
      (fun target => ensureTypeWith id (.occurrence node.id.occurrence) .word target) with
  | error err => simp [checked, bind, Except.bind] at accepted
  | ok rawValidated =>
    simp only [checked, bind, Except.bind, pure, Pure.pure, Except.pure,
      Except.ok.injEq] at accepted
    subst validated
    unfold validateIntegerLiteralResolutionWith at checked
    split at checked
    · simp [failWith] at checked
    · rename_i target
      split at checked
      · simp [failWith] at checked
      · rename_i requirements
        cases decodedEq : numericLiteralValue? source with
        | none => simp [decodedEq, failWith, bind, Except.bind] at checked
        | some decoded =>
          simp only [decodedEq, bind, Except.bind, pure, Pure.pure, Except.pure] at checked
          split at checked
          · simp [failWith] at checked
          · rename_i raw
            cases lowered : lowerType (.occurrence node.id.occurrence) resolution.targetType with
            | error err => simp [ensureTypeWith, lowered, Except.mapError, bind, Except.bind] at checked
            | ok coreType =>
              by_cases wordType : coreType = .word
              · subst coreType
                simp only [ensureTypeWith, lowered, Except.mapError, ↓reduceIte,
                  bind, Except.bind, pure, Pure.pure, Except.pure] at checked
                cases found : exactIntegerLiteralRequirementWith id (.occurrence node.id.occurrence)
                    solvedRequirements resolution.requirement with
                | error err => simp [found] at checked
                | ok solved =>
                  simp only [found] at checked
                  split at checked
                  · simp [failWith] at checked
                  · rename_i predicate
                    split at checked
                    · simp [failWith] at checked
                    · rename_i goal
                      split at checked
                      · simp [failWith] at checked
                      · split at checked
                        · simp [failWith] at checked
                        · split at checked
                          · simp [failWith] at checked
                          · simp only [Except.ok.injEq] at checked
                            subst rawValidated
                            have targetWord := lowerType_word_source lowered
                            have targetEq : resolution.targetType = node.type := by simpa using target
                            have attached : node.requirements = [resolution.requirement] := by simpa using requirements
                            have rawEq : decoded = resolution.rawValue := by simpa using raw
                            have predicateEq : solved.predicate = ProgramSignatures.builtinIntPredicate .word :=
                              builtinWordPredicate_of_beq (by simpa [bne, IntegerLiteralResolution.predicate, targetWord] using predicate)
                            have solvedMember := exactIntegerLiteralRequirementWith_member found
                            exact ⟨targetWord, targetEq ▸ targetWord, attached, emptyCoercions,
                              numericLiteralValue?_sound (rawEq ▸ decodedEq), rfl, rfl,
                              ⟨solved, solvedMember.1, solvedMember.2, predicateEq⟩⟩
              · simp [ensureTypeWith, lowered, wordType, Except.mapError, failWith, bind, Except.bind] at checked


/-- The native Integer validator establishes the same source metadata facts as
its Word counterpart while retaining the exact unbounded integer value. -/
structure NativeIntegerLiteralCertificate
    (solvedRequirements : List SolvedRequirement) (node : ExpressionNode)
    (source : Syntax.CoreLiteralValue) (resolution : IntegerLiteralResolution)
    (validated : NativeIntegerLiteral) : Prop where
  targetType : resolution.targetType = .integer
  nodeType : node.type = .integer
  requirements : node.requirements = [resolution.requirement]
  coercions : node.coercions = []
  meaning : NumericLiteralDenotes source resolution.rawValue
  value : validated.value = Int.ofNat resolution.rawValue
  consumedRequirements : validated.consumedRequirements = [resolution.requirement]
  solved : ∃ solved ∈ solvedRequirements, solved.id = resolution.requirement ∧
    solved.predicate = ProgramSignatures.builtinIntPredicate .integer

private theorem builtinIntegerPredicate_of_beq {predicate : ProgramPredicate}
    (equal : (predicate == ProgramSignatures.builtinIntPredicate .integer) = true) :
    predicate = ProgramSignatures.builtinIntPredicate .integer := by
  cases predicate with
  | mk trait subject arguments =>
    cases trait with
    | builtin builtin =>
      cases builtin
      change ((subject == .integer) && (arguments == [])) = true at equal
      simp only [Bool.and_eq_true, beq_iff_eq] at equal
      rcases equal with ⟨rfl, rfl⟩
      rfl
    | declaration id =>
      change false = true at equal
      contradiction

theorem validateNativeIntegerLiteral_sound
    {solvedRequirements : List SolvedRequirement} {node : ExpressionNode}
    {source : Syntax.CoreLiteralValue} {resolution : IntegerLiteralResolution}
    {validated : NativeIntegerLiteral}
    (accepted : validateNativeIntegerLiteral solvedRequirements node source resolution = .ok validated) :
    NativeIntegerLiteralCertificate solvedRequirements node source resolution validated := by
  have emptyCoercions : node.coercions = [] := by
    by_cases empty : node.coercions = []
    · exact empty
    · simp [validateNativeIntegerLiteral, empty, fail, bind, Except.bind] at accepted
  simp only [validateNativeIntegerLiteral, emptyCoercions, List.isEmpty_nil, ↓reduceIte] at accepted
  cases checked : validateIntegerLiteralResolutionWith id (.occurrence node.id.occurrence)
      solvedRequirements node.type node.requirements source resolution (.builtin .intInteger)
      (fun target => if target = Ty.integer then pure ()
        else fail (.occurrence node.id.occurrence) (.unsupportedType target)) with
  | error err => simp [checked, bind, Except.bind] at accepted
  | ok rawValidated =>
    simp only [pure, Pure.pure, Except.pure] at checked
    simp only [checked, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    subst validated
    unfold validateIntegerLiteralResolutionWith at checked
    split at checked
    · simp [failWith] at checked
    · rename_i target
      split at checked
      · simp [failWith] at checked
      · rename_i requirements
        cases decodedEq : numericLiteralValue? source with
        | none => simp [decodedEq, failWith, bind, Except.bind] at checked
        | some decoded =>
          simp only [decodedEq, bind, Except.bind, pure, Pure.pure, Except.pure] at checked
          split at checked
          · simp [failWith] at checked
          · rename_i raw
            by_cases targetInteger : resolution.targetType = Ty.integer
            · simp only [targetInteger, ↓reduceIte] at checked
              cases found : exactIntegerLiteralRequirementWith id (.occurrence node.id.occurrence)
                  solvedRequirements resolution.requirement with
              | error err => simp [found] at checked
              | ok solved =>
                simp only [found] at checked
                split at checked
                · simp [failWith] at checked
                · rename_i predicate
                  split at checked
                  · simp [failWith] at checked
                  · split at checked
                    · simp [failWith] at checked
                    · split at checked
                      · simp [failWith] at checked
                      · split at checked
                        · simp [failWith] at checked
                        · simp only [Except.ok.injEq] at checked
                          subst rawValidated
                          have targetEq : resolution.targetType = node.type := by simpa using target
                          have attached : node.requirements = [resolution.requirement] := by simpa using requirements
                          have rawEq : decoded = resolution.rawValue := by simpa using raw
                          have predicateEq : solved.predicate = ProgramSignatures.builtinIntPredicate .integer :=
                            builtinIntegerPredicate_of_beq (by simpa [bne, IntegerLiteralResolution.predicate, targetInteger] using predicate)
                          have solvedMember := exactIntegerLiteralRequirementWith_member found
                          exact ⟨targetInteger, targetEq ▸ targetInteger, attached, emptyCoercions,
                            numericLiteralValue?_sound (rawEq ▸ decodedEq), rfl, rfl,
                            ⟨solved, solvedMember.1, solvedMember.2, predicateEq⟩⟩
            · simp [targetInteger, fail] at checked

end Solcore.Frontend.SourceCoreElaboration

/-! Static receipts for the existing closed staged evaluator. Validation visits
both conditional branches, including when execution is disabled. These receipts
retain that visitation order and do not assign source execution meaning to the
placeholder values produced in validation mode. -/
namespace Solcore.Frontend.SourceCoreElaboration.Internal.Staged
open SourceInference TypeSystem

/-- The existing function-local carrier, with no change to its private ABI. -/
abbrev Binding := StagedIntegerBinding
abbrev Environment := StagedIntegerEnvironment
abbrev BinaryOperation := StagedIntegerBinaryOperation
abbrev Comparison := StagedIntegerComparison
abbrev binaryOperation? := stagedIntegerBinaryOperation?
abbrev comparison? := stagedIntegerComparison?
abbrev applyBinary := applyStagedIntegerBinary
abbrev applyComparison := applyStagedIntegerComparison
abbrev lookup := StagedIntegerEnvironment.lookup?

/-- Fuel and validation-mode interfaces to the original mutual implementation.
The original public entry points use an empty environment and execution mode. -/
def integer (solved : List SolvedRequirement) (source : TypedSource)
    (environment : Environment) (execute : Bool) (fuel : Nat) (expression : ExpressionId) :
    Except Error StagedIntegerEvaluation :=
  evaluateStagedIntegerFuelWith id (rejectStagedIntegerCallsWith id)
    solved source environment execute fuel expression

def word (solved : List SolvedRequirement) (source : TypedSource)
    (environment : Environment) (execute : Bool) (fuel : Nat) (expression : ExpressionId) :
    Except Error StagedWordEvaluation :=
  evaluateStagedWordFuelWith id (rejectStagedIntegerCallsWith id)
    solved source environment execute fuel expression

def bool (solved : List SolvedRequirement) (source : TypedSource)
    (environment : Environment) (execute : Bool) (fuel : Nat) (expression : ExpressionId) :
    Except Error StagedBoolEvaluation :=
  evaluateStagedBoolFuelWith id (rejectStagedIntegerCallsWith id)
    solved source environment execute fuel expression

/-- The complete existing builtin validator is retained, including actual
callee spelling, type, arity, and the ordered argument type checks. -/
structure BuiltinChecked (source : TypedSource) (node : ExpressionNode)
    (callee : ExpressionId) (arguments : List ExpressionId) (function : BuiltinFunctionId) : Prop where
  accepted : validateBuiltinFunctionCall source node callee arguments function = .ok ()
  requirements : node.requirements = []
  coercions : node.coercions = []

mutual
  inductive IntegerChecked (solved : List SolvedRequirement) (source : TypedSource)
      (environment : Environment) : Bool → Nat → ExpressionId → StagedIntegerEvaluation → Prop where
    | literal {execute : Bool} {fuel : Nat} {expression : ExpressionId} {node : ExpressionNode}
        {literal : Syntax.CoreLiteralValue} {resolution : IntegerLiteralResolution} {validated : NativeIntegerLiteral}
        (found : source.lookupExpression? expression = some node)
        (form : node.form = .integerLiteral literal resolution)
        (accepted : validateNativeIntegerLiteral solved node literal resolution = .ok validated) :
        IntegerChecked solved source environment execute (fuel + 1) expression
          ⟨validated.value, validated.consumedRequirements⟩
    | local {execute : Bool} {fuel : Nat} {expression : ExpressionId} {node : ExpressionNode}
        {name : String} {binder : Resolved.LocalId} {binding : Binding}
        (found : source.lookupExpression? expression = some node)
        (form : node.form = .reference name (.local binder))
        (typed : node.type = .integer) (requirements : node.requirements = []) (coercions : node.coercions = [])
        (owned : binder.owner = source.owner) (selected : lookup environment binder = some binding)
        (binderOwned : binding.binder.id.owner = source.owner)
        (monomorphic : binding.binder.scheme.quantified = [])
        (binderType : binding.binder.scheme.body = .integer) (spelling : name = binding.binder.name) :
        IntegerChecked solved source environment execute (fuel + 1) expression ⟨binding.value, []⟩
    | group {execute : Bool} {fuel : Nat} {expression inner : ExpressionId} {node : ExpressionNode}
        {result : StagedIntegerEvaluation}
        (found : source.lookupExpression? expression = some node) (form : node.form = .group inner)
        (typed : node.type = .integer) (requirements : node.requirements = []) (coercions : node.coercions = [])
        (child : IntegerChecked solved source environment execute fuel inner result) :
        IntegerChecked solved source environment execute (fuel + 1) expression result
    | binary {execute : Bool} {fuel : Nat} {expression callee left right : ExpressionId} {node : ExpressionNode}
        {function : BuiltinFunctionId} {operation : BinaryOperation} {a b : StagedIntegerEvaluation}
        (found : source.lookupExpression? expression = some node)
        (form : node.form = .call callee [left, right] (.builtinFunction function))
        (operationEq : binaryOperation? function = some operation)
        (validated : BuiltinChecked source node callee [left, right] function)
        (leftChecked : IntegerChecked solved source environment execute fuel left a)
        (rightChecked : IntegerChecked solved source environment execute fuel right b) :
        IntegerChecked solved source environment execute (fuel + 1) expression
          ⟨if execute then applyBinary operation a.value b.value else 0,
            a.consumedRequirements ++ b.consumedRequirements⟩
    | fromWord {execute : Bool} {fuel : Nat} {expression callee argument : ExpressionId} {node : ExpressionNode}
        {child : StagedWordEvaluation}
        (found : source.lookupExpression? expression = some node)
        (form : node.form = .call callee [argument] (.builtinFunction .wordToInteger))
        (validated : BuiltinChecked source node callee [argument] .wordToInteger)
        (checked : WordChecked solved source environment execute fuel argument child) :
        IntegerChecked solved source environment execute (fuel + 1) expression
          ⟨if execute then Int.ofNat child.value.val else 0, child.consumedRequirements⟩
    | conditional {execute : Bool} {fuel : Nat} {expression condition yes no : ExpressionId} {node : ExpressionNode}
        {guard : StagedBoolEvaluation} {left right : StagedIntegerEvaluation}
        (found : source.lookupExpression? expression = some node)
        (form : node.form = .conditional condition yes no)
        (typed : node.type = .integer) (requirements : node.requirements = []) (coercions : node.coercions = [])
        (conditionChecked : BoolChecked solved source environment execute fuel condition guard)
        (thenChecked : IntegerChecked solved source environment (execute && guard.value) fuel yes left)
        (elseChecked : IntegerChecked solved source environment (execute && !guard.value) fuel no right) :
        IntegerChecked solved source environment execute (fuel + 1) expression
          ⟨if guard.value then left.value else right.value,
            guard.consumedRequirements ++ left.consumedRequirements ++ right.consumedRequirements⟩

  inductive WordChecked (solved : List SolvedRequirement) (source : TypedSource)
      (environment : Environment) : Bool → Nat → ExpressionId → StagedWordEvaluation → Prop where
    | literal {execute : Bool} {fuel : Nat} {expression : ExpressionId} {node : ExpressionNode}
        {literal : Syntax.CoreLiteralValue} {resolution : IntegerLiteralResolution} {validated : WordIntegerLiteral}
        (found : source.lookupExpression? expression = some node)
        (form : node.form = .integerLiteral literal resolution)
        (accepted : validateWordIntegerLiteral solved node literal resolution = .ok validated) :
        WordChecked solved source environment execute (fuel + 1) expression
          ⟨validated.value, validated.consumedRequirements⟩
    | group {execute : Bool} {fuel : Nat} {expression inner : ExpressionId} {node : ExpressionNode}
        {result : StagedWordEvaluation}
        (found : source.lookupExpression? expression = some node) (form : node.form = .group inner)
        (typed : node.type = .word) (requirements : node.requirements = []) (coercions : node.coercions = [])
        (child : WordChecked solved source environment execute fuel inner result) :
        WordChecked solved source environment execute (fuel + 1) expression result
    | fromInteger {execute : Bool} {fuel : Nat} {expression callee argument : ExpressionId} {node : ExpressionNode}
        {child : StagedIntegerEvaluation}
        (found : source.lookupExpression? expression = some node)
        (form : node.form = .call callee [argument] (.builtinFunction .wordFromInteger))
        (validated : BuiltinChecked source node callee [argument] .wordFromInteger)
        (checked : IntegerChecked solved source environment execute fuel argument child) :
        WordChecked solved source environment execute (fuel + 1) expression
          ⟨if execute then Core.Word.ofIntModulo child.value else Core.Word.ofNatModulo 0, child.consumedRequirements⟩
    | conditional {execute : Bool} {fuel : Nat} {expression condition yes no : ExpressionId} {node : ExpressionNode}
        {guard : StagedBoolEvaluation} {left right : StagedWordEvaluation}
        (found : source.lookupExpression? expression = some node)
        (form : node.form = .conditional condition yes no)
        (typed : node.type = .word) (requirements : node.requirements = []) (coercions : node.coercions = [])
        (conditionChecked : BoolChecked solved source environment execute fuel condition guard)
        (thenChecked : WordChecked solved source environment (execute && guard.value) fuel yes left)
        (elseChecked : WordChecked solved source environment (execute && !guard.value) fuel no right) :
        WordChecked solved source environment execute (fuel + 1) expression
          ⟨if guard.value then left.value else right.value,
            guard.consumedRequirements ++ left.consumedRequirements ++ right.consumedRequirements⟩

  inductive BoolChecked (solved : List SolvedRequirement) (source : TypedSource)
      (environment : Environment) : Bool → Nat → ExpressionId → StagedBoolEvaluation → Prop where
    | literal {execute : Bool} {fuel : Nat} {expression : ExpressionId} {node : ExpressionNode} {name : String} {value : Bool}
        (found : source.lookupExpression? expression = some node)
        (form : node.form = .reference name (.builtinBoolean value))
        (typed : node.type = .bool) (requirements : node.requirements = []) (coercions : node.coercions = [])
        (spelling : name = if value then "true" else "false") :
        BoolChecked solved source environment execute (fuel + 1) expression ⟨value, []⟩
    | group {execute : Bool} {fuel : Nat} {expression inner : ExpressionId} {node : ExpressionNode}
        {result : StagedBoolEvaluation}
        (found : source.lookupExpression? expression = some node) (form : node.form = .group inner)
        (typed : node.type = .bool) (requirements : node.requirements = []) (coercions : node.coercions = [])
        (child : BoolChecked solved source environment execute fuel inner result) :
        BoolChecked solved source environment execute (fuel + 1) expression result
    | comparison {execute : Bool} {fuel : Nat} {expression callee left right : ExpressionId} {node : ExpressionNode}
        {function : BuiltinFunctionId} {operation : Comparison} {a b : StagedIntegerEvaluation}
        (found : source.lookupExpression? expression = some node)
        (form : node.form = .call callee [left, right] (.builtinFunction function))
        (operationEq : comparison? function = some operation)
        (validated : BuiltinChecked source node callee [left, right] function)
        (leftChecked : IntegerChecked solved source environment execute fuel left a)
        (rightChecked : IntegerChecked solved source environment execute fuel right b) :
        BoolChecked solved source environment execute (fuel + 1) expression
          ⟨if execute then applyComparison operation a.value b.value else false,
            a.consumedRequirements ++ b.consumedRequirements⟩
    | conditional {execute : Bool} {fuel : Nat} {expression condition yes no : ExpressionId} {node : ExpressionNode}
        {guard left right : StagedBoolEvaluation}
        (found : source.lookupExpression? expression = some node)
        (form : node.form = .conditional condition yes no)
        (typed : node.type = .bool) (requirements : node.requirements = []) (coercions : node.coercions = [])
        (conditionChecked : BoolChecked solved source environment execute fuel condition guard)
        (thenChecked : BoolChecked solved source environment (execute && guard.value) fuel yes left)
        (elseChecked : BoolChecked solved source environment (execute && !guard.value) fuel no right) :
        BoolChecked solved source environment execute (fuel + 1) expression
          ⟨if guard.value then left.value else right.value,
            guard.consumedRequirements ++ left.consumedRequirements ++ right.consumedRequirements⟩
end


set_option linter.unusedSimpArgs false

private theorem lookup_success {source : TypedSource} {expression : ExpressionId} {node : ExpressionNode}
    (accepted : lookupExpression source expression = .ok node) :
    source.lookupExpression? expression = some node := by
  unfold lookupExpression at accepted
  split at accepted <;> simp_all [fail, TypedSource.lookupExpression?]

private theorem builtin_checked {source : TypedSource} {node : ExpressionNode}
    {callee : ExpressionId} {arguments : List ExpressionId} {function : BuiltinFunctionId}
    (accepted : validateBuiltinFunctionCallWith id source node callee arguments function = .ok ()) :
    BuiltinChecked source node callee arguments function := by
  have requirements : node.requirements = [] := by
    by_cases same : node.requirements = []
    · exact same
    · simp [validateBuiltinFunctionCallWith, same, failWith, bind, Except.bind] at accepted
  have coercions : node.coercions = [] := by
    by_cases same : node.coercions = []
    · exact same
    · simp [validateBuiltinFunctionCallWith, requirements, same, failWith, bind, Except.bind] at accepted
  exact ⟨accepted, requirements, coercions⟩

/-- Successful metadata validation is independent of the error location and
can replace the target checker by another checker accepting this same target. -/
private theorem literal_recheck {site otherSite : ErrorSite}
    {solved : List SolvedRequirement} {nodeType : Ty} {attached : List RequirementId}
    {literal : Syntax.CoreLiteralValue} {resolution : IntegerLiteralResolution}
    {implementation : ProgramImplId} {check otherCheck : Ty → Except Error Unit}
    {validated : ValidatedIntegerLiteral}
    (accepted : validateIntegerLiteralResolutionWith id site solved nodeType attached literal resolution
      implementation check = .ok validated)
    (target : otherCheck resolution.targetType = .ok ()) :
    validateIntegerLiteralResolutionWith id otherSite solved nodeType attached literal resolution
      implementation otherCheck = .ok validated := by
  unfold validateIntegerLiteralResolutionWith at accepted ⊢
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at accepted ⊢
  repeat' (split at accepted <;>
    simp_all [failWith, exactIntegerLiteralRequirementWith, bind, Except.bind, pure, Pure.pure, Except.pure])
  all_goals cases decoded : numericLiteralValue? literal <;>
    simp_all [failWith, exactIntegerLiteralRequirementWith, bind, Except.bind, pure, Pure.pure, Except.pure]
  all_goals repeat' (split at accepted <;>
    simp_all [failWith, bind, Except.bind, pure, Pure.pure, Except.pure])


  all_goals cases checked : check nodeType <;>
    simp_all [failWith, bind, Except.bind, pure, Pure.pure, Except.pure]
  all_goals
    cases rows : solved.filter (fun row => decide (row.id = resolution.requirement)) with
    | nil => simp_all
    | cons row tail =>
      cases tail with
      | cons other rest => simp_all
      | nil =>
        simp_all
        cases evidence : row.evidence with
        | assumption predicate =>
          simp_all
          repeat' (split at accepted <;> simp_all)
        | implementation proof =>
          cases proof with
          | byImpl goal impl premises =>
            simp_all
            repeat' (split at accepted <;> simp_all)

private theorem literal_target {site : ErrorSite}
    {solved : List SolvedRequirement} {nodeType : Ty} {attached : List RequirementId}
    {literal : Syntax.CoreLiteralValue} {resolution : IntegerLiteralResolution}
    {implementation : ProgramImplId} {check : Ty → Except Error Unit}
    {validated : ValidatedIntegerLiteral}
    (accepted : validateIntegerLiteralResolutionWith id site solved nodeType attached literal resolution
      implementation check = .ok validated) : resolution.targetType = nodeType := by
  unfold validateIntegerLiteralResolutionWith at accepted
  split at accepted
  · simp [failWith] at accepted
  · rename_i equal
    simpa [bne_iff_ne] using equal

private theorem integer_literal_checked {site : ErrorSite}
    {solved : List SolvedRequirement} {node : ExpressionNode}
    {literal : Syntax.CoreLiteralValue} {resolution : IntegerLiteralResolution}
    {validated : ValidatedIntegerLiteral}
    (coercions : node.coercions = []) (typed : node.type = .integer)
    (accepted : validateIntegerLiteralResolutionWith id site solved node.type node.requirements literal resolution
      (.builtin .intInteger) (fun target => if target = Ty.integer then pure ()
        else failWith id site (.stagedIntegerTypeMismatch .integer target)) = .ok validated) :
    validateNativeIntegerLiteral solved node literal resolution =
      .ok ⟨Int.ofNat validated.rawValue, validated.consumedRequirements⟩ := by
  have target := (literal_target accepted).trans typed
  have checked := literal_recheck (otherSite := .occurrence node.id.occurrence)
    (otherCheck := fun target => if target = Ty.integer then pure ()
      else fail (.occurrence node.id.occurrence) (.unsupportedType target)) accepted (by simp [target])
  simp only [pure, Pure.pure, Except.pure] at checked
  simp only [validateNativeIntegerLiteral, coercions, List.isEmpty_nil, Bool.not_true,
    ↓reduceIte, checked, bind, Except.bind, pure, Pure.pure, Except.pure]

private theorem word_literal_checked {site : ErrorSite}
    {solved : List SolvedRequirement} {node : ExpressionNode}
    {literal : Syntax.CoreLiteralValue} {resolution : IntegerLiteralResolution}
    {validated : ValidatedIntegerLiteral}
    (coercions : node.coercions = []) (typed : node.type = .word)
    (accepted : validateIntegerLiteralResolutionWith id site solved node.type node.requirements literal resolution
      (.builtin .intWord) (fun target => if target = Ty.word then pure ()
        else failWith id site (.stagedWordTypeMismatch .word target)) = .ok validated) :
    validateWordIntegerLiteral solved node literal resolution =
      .ok ⟨Core.Word.ofNatModulo validated.rawValue, validated.consumedRequirements⟩ := by
  have target := (literal_target accepted).trans typed
  have checked := literal_recheck (otherSite := .occurrence node.id.occurrence)
    (otherCheck := fun target => ensureTypeWith id (.occurrence node.id.occurrence) .word target)
    accepted (by simp [target, ensureTypeWith, lowerType, Ty.word, Except.mapError, bind, Except.bind, pure, Pure.pure, Except.pure])
  simp only [validateWordIntegerLiteral, coercions, List.isEmpty_nil, Bool.not_true,
    ↓reduceIte, validateWordIntegerLiteralWith, checked, bind, Except.bind, pure, Pure.pure, Except.pure]

private theorem binder_checked {site : ErrorSite} {source : TypedSource} {binder : TypedBinder}
    (accepted : validateStagedIntegerBinderWith id site source binder = .ok ()) :
    binder.id.owner = source.owner ∧ binder.scheme.quantified = [] ∧ binder.scheme.body = .integer := by
  unfold validateStagedIntegerBinderWith at accepted
  repeat' split at accepted
  all_goals simp_all [failWith, bne_iff_ne]

private theorem word_step {solved : List SolvedRequirement} {source : TypedSource} {environment : Environment}
    {fuel : Nat}
    (integers : ∀ execute expression result, integer solved source environment execute fuel expression = .ok result →
      IntegerChecked solved source environment execute fuel expression result)
    (words : ∀ execute expression result, word solved source environment execute fuel expression = .ok result →
      WordChecked solved source environment execute fuel expression result)
    (bools : ∀ execute expression result, bool solved source environment execute fuel expression = .ok result →
      BoolChecked solved source environment execute fuel expression result)
    {execute : Bool} {expression : ExpressionId} {result : StagedWordEvaluation}
    (accepted : word solved source environment execute (fuel + 1) expression = .ok result) :
    WordChecked solved source environment execute (fuel + 1) expression result := by
  simp only [word, evaluateStagedWordFuelWith] at accepted
  cases found : lookupExpression source expression with
  | error error => simp [found, Except.mapError, bind, Except.bind] at accepted
  | ok node =>
    simp only [found, Except.mapError, id, bind, Except.bind] at accepted
    have found' := lookup_success found
    split at accepted
    · rename_i callee arguments form
      cases validated : validateBuiltinFunctionCallWith id source node callee arguments .wordFromInteger with
      | error error => simp [validated] at accepted
      | ok checked =>
        cases checked
        simp only [validated] at accepted
        split at accepted
        · rename_i argument
          cases evaluated : evaluateStagedIntegerFuelWith id (rejectStagedIntegerCallsWith id)
              solved source environment execute fuel argument with
          | error error => simp [evaluated] at accepted
          | ok child =>
            simp only [evaluated, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
            subst result
            exact .fromInteger found' form (builtin_checked validated) (integers _ _ _ evaluated)
        · simp [failWith] at accepted
    · have coercions : node.coercions = [] := by
        by_cases same : node.coercions = []
        · exact same
        · simp [same, failWith, bind, Except.bind] at accepted
      have typed : node.type = .word := by
        by_cases same : node.type = .word
        · exact same
        · simp [coercions, same, failWith, bind, Except.bind] at accepted
      simp only [coercions, List.isEmpty_nil, ↓reduceIte, typed, bne_self_eq_false,
        Bool.false_eq_true, pure, Pure.pure, Except.pure, bind, Except.bind, failWith] at accepted
      split at accepted
      · rename_i literal resolution form
        cases evaluated : validateIntegerLiteralResolutionWith id (.occurrence expression.occurrence) solved node.type
            node.requirements literal resolution (.builtin .intWord) (fun target =>
              if target = Ty.word then pure ()
              else failWith id (.occurrence expression.occurrence) (.stagedWordTypeMismatch .word target)) with
        | error error =>
          simp only [typed, pure, Pure.pure, Except.pure, failWith, id] at evaluated
          simp [evaluated] at accepted
        | ok child =>
          have checked := word_literal_checked coercions typed evaluated
          simp only [typed, pure, Pure.pure, Except.pure, failWith, id] at evaluated
          dsimp only [id] at accepted evaluated
          rw [evaluated] at accepted
          simp only [Except.ok.injEq] at accepted
          subst result
          exact .literal found' form checked
      · rename_i inner form
        have requirements : node.requirements = [] := by
          by_cases same : node.requirements = []
          · exact same
          · simp [same, failWith] at accepted
        simp only [requirements, List.isEmpty_nil, ↓reduceIte] at accepted
        exact .group found' form typed requirements coercions (words _ _ _ accepted)
      · rename_i condition yes no form
        have requirements : node.requirements = [] := by
          by_cases same : node.requirements = []
          · exact same
          · simp [same, failWith, bind, Except.bind] at accepted
        simp only [requirements, List.isEmpty_nil, ↓reduceIte] at accepted
        cases guardEq : evaluateStagedBoolFuelWith id (rejectStagedIntegerCallsWith id)
            solved source environment execute fuel condition with
        | error error => simp [guardEq] at accepted
        | ok guard =>
          simp only [guardEq] at accepted
          cases leftEq : evaluateStagedWordFuelWith id (rejectStagedIntegerCallsWith id)
              solved source environment (execute && guard.value) fuel yes with
          | error error => simp [leftEq] at accepted
          | ok left =>
            simp only [leftEq] at accepted
            cases rightEq : evaluateStagedWordFuelWith id (rejectStagedIntegerCallsWith id)
                solved source environment (execute && !guard.value) fuel no with
            | error error => simp [rightEq] at accepted
            | ok right =>
              simp only [rightEq, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
              subst result
              exact .conditional found' form typed requirements coercions
                (bools _ _ _ guardEq) (words _ _ _ leftEq) (words _ _ _ rightEq)
      · simp [failWith] at accepted

private theorem bool_step {solved : List SolvedRequirement} {source : TypedSource} {environment : Environment}
    {fuel : Nat}
    (integers : ∀ execute expression result, integer solved source environment execute fuel expression = .ok result →
      IntegerChecked solved source environment execute fuel expression result)
    (bools : ∀ execute expression result, bool solved source environment execute fuel expression = .ok result →
      BoolChecked solved source environment execute fuel expression result)
    {execute : Bool} {expression : ExpressionId} {result : StagedBoolEvaluation}
    (accepted : bool solved source environment execute (fuel + 1) expression = .ok result) :
    BoolChecked solved source environment execute (fuel + 1) expression result := by
  simp only [bool, evaluateStagedBoolFuelWith] at accepted
  cases found : lookupExpression source expression with
  | error error => simp [found, Except.mapError, bind, Except.bind] at accepted
  | ok node =>
    simp only [found, Except.mapError, id, bind, Except.bind] at accepted
    have found' := lookup_success found
    split at accepted
    · rename_i callee arguments function form
      cases operationEq : stagedIntegerComparison? function with
      | none =>
        simp only [operationEq, failWith, id, bind, Except.bind] at accepted
        repeat' split at accepted
        all_goals simp_all
      | some operation =>
        simp only [operationEq] at accepted
        cases validated : validateBuiltinFunctionCallWith id source node callee arguments function with
        | error error => simp [validated] at accepted
        | ok checked =>
          cases checked
          simp only [validated] at accepted
          split at accepted
          · rename_i left right
            cases leftEq : evaluateStagedIntegerFuelWith id (rejectStagedIntegerCallsWith id)
                solved source environment execute fuel left with
            | error error => simp [leftEq] at accepted
            | ok a =>
              simp only [leftEq] at accepted
              cases rightEq : evaluateStagedIntegerFuelWith id (rejectStagedIntegerCallsWith id)
                  solved source environment execute fuel right with
              | error error => simp [rightEq] at accepted
              | ok b =>
                simp only [rightEq, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
                subst result
                exact .comparison found' form operationEq (builtin_checked validated)
                  (integers _ _ _ leftEq) (integers _ _ _ rightEq)
          · simp [failWith] at accepted
    · have coercions : node.coercions = [] := by
        by_cases same : node.coercions = []
        · exact same
        · simp [same, failWith, bind, Except.bind] at accepted
      have typed : node.type = .bool := by
        by_cases same : node.type = .bool
        · exact same
        · simp [coercions, same, failWith, bind, Except.bind] at accepted
      have requirements : node.requirements = [] := by
        by_cases same : node.requirements = []
        · exact same
        · simp [coercions, typed, same, failWith, bind, Except.bind] at accepted
      simp only [coercions, requirements, List.isEmpty_nil, ↓reduceIte, typed, bne_self_eq_false,
        Bool.false_eq_true, pure, Pure.pure, Except.pure, bind, Except.bind, failWith, id] at accepted
      split at accepted
      · rename_i name value form
        by_cases spelling : name = builtinBooleanSpelling value
        · simp only [spelling, ↓reduceIte, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
          subst result
          exact .literal found' form typed requirements coercions spelling
        · simp [spelling] at accepted
      · rename_i inner form
        exact .group found' form typed requirements coercions (bools _ _ _ accepted)
      · rename_i condition yes no form
        cases guardEq : evaluateStagedBoolFuelWith id (rejectStagedIntegerCallsWith id)
            solved source environment execute fuel condition with
        | error error => simp [guardEq] at accepted
        | ok guard =>
          simp only [guardEq] at accepted
          cases leftEq : evaluateStagedBoolFuelWith id (rejectStagedIntegerCallsWith id)
              solved source environment (execute && guard.value) fuel yes with
          | error error => simp [leftEq] at accepted
          | ok left =>
            simp only [leftEq] at accepted
            cases rightEq : evaluateStagedBoolFuelWith id (rejectStagedIntegerCallsWith id)
                solved source environment (execute && !guard.value) fuel no with
            | error error => simp [rightEq] at accepted
            | ok right =>
              simp only [rightEq, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
              subst result
              exact .conditional found' form typed requirements coercions
                (bools _ _ _ guardEq) (bools _ _ _ leftEq) (bools _ _ _ rightEq)
      · simp [failWith] at accepted

private theorem integer_step {solved : List SolvedRequirement} {source : TypedSource} {environment : Environment}
    {fuel : Nat}
    (integers : ∀ execute expression result, integer solved source environment execute fuel expression = .ok result →
      IntegerChecked solved source environment execute fuel expression result)
    (words : ∀ execute expression result, word solved source environment execute fuel expression = .ok result →
      WordChecked solved source environment execute fuel expression result)
    (bools : ∀ execute expression result, bool solved source environment execute fuel expression = .ok result →
      BoolChecked solved source environment execute fuel expression result)
    {execute : Bool} {expression : ExpressionId} {result : StagedIntegerEvaluation}
    (accepted : integer solved source environment execute (fuel + 1) expression = .ok result) :
    IntegerChecked solved source environment execute (fuel + 1) expression result := by
  simp only [integer, evaluateStagedIntegerFuelWith] at accepted
  cases found : lookupExpression source expression with
  | error error => simp [found, Except.mapError, bind, Except.bind] at accepted
  | ok node =>
    simp only [found, Except.mapError, id, bind, Except.bind] at accepted
    have found' := lookup_success found
    split at accepted
    · rename_i callee arguments form
      cases validated : validateBuiltinFunctionCallWith id source node callee arguments .wordToInteger with
      | error error => simp [validated] at accepted
      | ok checked =>
        cases checked
        simp only [validated] at accepted
        split at accepted
        · rename_i argument
          cases evaluated : evaluateStagedWordFuelWith id (rejectStagedIntegerCallsWith id)
              solved source environment execute fuel argument with
          | error error => simp [evaluated] at accepted
          | ok child =>
            simp only [evaluated, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
            subst result
            exact .fromWord found' form (builtin_checked validated) (words _ _ _ evaluated)
        · simp [failWith] at accepted
    · rename_i callee arguments function notConversion form
      cases operationEq : stagedIntegerBinaryOperation? function with
      | none =>
        simp only [operationEq, failWith, id, bind, Except.bind] at accepted
        repeat' split at accepted
        all_goals simp_all
      | some operation =>
        simp only [operationEq] at accepted
        cases validated : validateBuiltinFunctionCallWith id source node callee arguments function with
        | error error => simp [validated] at accepted
        | ok checked =>
          cases checked
          simp only [validated] at accepted
          split at accepted
          · rename_i left right
            cases leftEq : evaluateStagedIntegerFuelWith id (rejectStagedIntegerCallsWith id)
                solved source environment execute fuel left with
            | error error => simp [leftEq] at accepted
            | ok a =>
              simp only [leftEq] at accepted
              cases rightEq : evaluateStagedIntegerFuelWith id (rejectStagedIntegerCallsWith id)
                  solved source environment execute fuel right with
              | error error => simp [rightEq] at accepted
              | ok b =>
                simp only [rightEq, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
                subst result
                exact .binary found' form operationEq (builtin_checked validated)
                  (integers _ _ _ leftEq) (integers _ _ _ rightEq)
          · simp [failWith] at accepted
    · simp only [rejectStagedIntegerCallsWith, failWith, id, bind, Except.bind] at accepted
      repeat' split at accepted
      all_goals simp_all
    · have coercions : node.coercions = [] := by
        by_cases same : node.coercions = []
        · exact same
        · simp [same, failWith, bind, Except.bind] at accepted
      have typed : node.type = .integer := by
        by_cases same : node.type = .integer
        · exact same
        · simp [coercions, same, failWith, bind, Except.bind] at accepted
      simp only [coercions, List.isEmpty_nil, ↓reduceIte, typed, bne_self_eq_false,
        Bool.false_eq_true, pure, Pure.pure, Except.pure, bind, Except.bind, failWith] at accepted
      split at accepted
      · rename_i literal resolution form
        cases evaluated : validateIntegerLiteralResolutionWith id (.occurrence expression.occurrence) solved node.type
            node.requirements literal resolution (.builtin .intInteger) (fun target =>
              if target = Ty.integer then pure ()
              else failWith id (.occurrence expression.occurrence) (.stagedIntegerTypeMismatch .integer target)) with
        | error error =>
          simp only [typed, pure, Pure.pure, Except.pure, failWith, id] at evaluated
          simp [evaluated] at accepted
        | ok child =>
          have checked := integer_literal_checked coercions typed evaluated
          simp only [typed, pure, Pure.pure, Except.pure, failWith, id] at evaluated
          dsimp only [id] at accepted evaluated
          rw [evaluated] at accepted
          simp only [Except.ok.injEq] at accepted
          subst result
          exact .literal found' form checked
      · rename_i name binder form
        have requirements : node.requirements = [] := by
          by_cases same : node.requirements = []
          · exact same
          · simp [same, failWith, bind, Except.bind] at accepted
        have owned : binder.owner = source.owner := by
          by_cases same : binder.owner = source.owner
          · exact same
          · simp [requirements, same, failWith, bind, Except.bind] at accepted
        simp only [requirements, List.isEmpty_nil, ↓reduceIte, owned, bne_self_eq_false,
          Bool.false_eq_true, pure, Pure.pure, Except.pure, bind, Except.bind] at accepted
        cases selected : StagedIntegerEnvironment.lookup? environment binder with
        | none => simp [selected, failWith] at accepted
        | some binding =>
          simp only [selected] at accepted
          cases checked : validateStagedIntegerBinderWith id (.occurrence expression.occurrence) source binding.binder with
          | error error => simp [checked] at accepted
          | ok checkedValue =>
            cases checkedValue
            simp only [checked] at accepted
            have binderFacts := binder_checked checked
            by_cases spelling : name = binding.binder.name
            · simp only [spelling, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
                pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
              subst result
              exact .local found' form typed requirements coercions owned selected
                binderFacts.1 binderFacts.2.1 binderFacts.2.2 spelling
            · simp [spelling, failWith] at accepted
      · rename_i inner form
        have requirements : node.requirements = [] := by
          by_cases same : node.requirements = []
          · exact same
          · simp [same, failWith] at accepted
        simp only [requirements, List.isEmpty_nil, ↓reduceIte] at accepted
        exact .group found' form typed requirements coercions (integers _ _ _ accepted)
      · rename_i condition yes no form
        have requirements : node.requirements = [] := by
          by_cases same : node.requirements = []
          · exact same
          · simp [same, failWith, bind, Except.bind] at accepted
        simp only [requirements, List.isEmpty_nil, ↓reduceIte] at accepted
        cases guardEq : evaluateStagedBoolFuelWith id (rejectStagedIntegerCallsWith id)
            solved source environment execute fuel condition with
        | error error => simp [guardEq] at accepted
        | ok guard =>
          simp only [guardEq] at accepted
          cases leftEq : evaluateStagedIntegerFuelWith id (rejectStagedIntegerCallsWith id)
              solved source environment (execute && guard.value) fuel yes with
          | error error => simp [leftEq] at accepted
          | ok left =>
            simp only [leftEq] at accepted
            cases rightEq : evaluateStagedIntegerFuelWith id (rejectStagedIntegerCallsWith id)
                solved source environment (execute && !guard.value) fuel no with
            | error error => simp [rightEq] at accepted
            | ok right =>
              simp only [rightEq, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
              subst result
              exact .conditional found' form typed requirements coercions
                (bools _ _ _ guardEq) (integers _ _ _ leftEq) (integers _ _ _ rightEq)
      · simp [failWith] at accepted

/-- One fuel induction extracts all three validation trees from the actual
mutual evaluator. Disabled branches retain their own checks and consumption. -/
theorem checked (solved : List SolvedRequirement) (source : TypedSource)
    (environment : Environment) (fuel : Nat) :
    (∀ execute expression result, integer solved source environment execute fuel expression = .ok result →
      IntegerChecked solved source environment execute fuel expression result) ∧
    (∀ execute expression result, word solved source environment execute fuel expression = .ok result →
      WordChecked solved source environment execute fuel expression result) ∧
    (∀ execute expression result, bool solved source environment execute fuel expression = .ok result →
      BoolChecked solved source environment execute fuel expression result) := by
  induction fuel with
  | zero =>
    constructor
    · intro execute expression result accepted
      simp [integer, evaluateStagedIntegerFuelWith, failWith] at accepted
    constructor
    · intro execute expression result accepted
      simp [word, evaluateStagedWordFuelWith, failWith] at accepted
    · intro execute expression result accepted
      simp [bool, evaluateStagedBoolFuelWith, failWith] at accepted
  | succ fuel ih =>
    exact ⟨fun _ _ _ accepted => integer_step ih.1 ih.2.1 ih.2.2 accepted,
      fun _ _ _ accepted => word_step ih.1 ih.2.1 ih.2.2 accepted,
      fun _ _ _ accepted => bool_step ih.1 ih.2.2 accepted⟩

theorem integer_checked {solved : List SolvedRequirement} {source : TypedSource}
    {environment : Environment} {execute : Bool} {fuel : Nat} {expression : ExpressionId}
    {result : StagedIntegerEvaluation}
    (accepted : integer solved source environment execute fuel expression = .ok result) :
    IntegerChecked solved source environment execute fuel expression result :=
  (checked solved source environment fuel).1 execute expression result accepted

theorem word_checked {solved : List SolvedRequirement} {source : TypedSource}
    {environment : Environment} {execute : Bool} {fuel : Nat} {expression : ExpressionId}
    {result : StagedWordEvaluation}
    (accepted : word solved source environment execute fuel expression = .ok result) :
    WordChecked solved source environment execute fuel expression result :=
  (checked solved source environment fuel).2.1 execute expression result accepted

theorem bool_checked {solved : List SolvedRequirement} {source : TypedSource}
    {environment : Environment} {execute : Bool} {fuel : Nat} {expression : ExpressionId}
    {result : StagedBoolEvaluation}
    (accepted : bool solved source environment execute fuel expression = .ok result) :
    BoolChecked solved source environment execute fuel expression result :=
  (checked solved source environment fuel).2.2 execute expression result accepted

/-- The existing public closed Integer entry uses this exact fuel, mode, and environment. -/
theorem evaluateStagedInteger_checked {solved : List SolvedRequirement} {source : TypedSource}
    {expression : ExpressionId} {result : StagedIntegerEvaluation}
    (accepted : evaluateStagedInteger solved source expression = .ok result) :
    IntegerChecked solved source [] true (source.nodes.length + 1) expression result :=
  integer_checked accepted

/-- All accepted Word conversions, groups, and conditional branches are covered. -/
theorem evaluateStagedWord_checked {solved : List SolvedRequirement} {source : TypedSource}
    {expression : ExpressionId} {result : StagedWordEvaluation}
    (accepted : evaluateStagedWord solved source expression = .ok result) :
    WordChecked solved source [] true (source.nodes.length + 1) expression result :=
  word_checked accepted

/-- All accepted comparisons and Bool conditionals use the same checked traversal. -/
theorem evaluateStagedBool_checked {solved : List SolvedRequirement} {source : TypedSource}
    {expression : ExpressionId} {result : StagedBoolEvaluation}
    (accepted : evaluateStagedBool solved source expression = .ok result) :
    BoolChecked solved source [] true (source.nodes.length + 1) expression result :=
  bool_checked accepted

end Solcore.Frontend.SourceCoreElaboration.Internal.Staged

/-! The closed Integer statement evaluator keeps validation and execution
separate. Every accepted branch remains in the static receipt, while source
execution later follows only the selected branch and records allocations. -/
namespace Solcore.Frontend.SourceCoreElaboration.Internal.Staged.Statements
open SourceInference TypeSystem

def bind (binder : TypedBinder) (value : Int) : Binding := ⟨binder, value⟩

def evaluate (solved : List SolvedRequirement) (source : TypedSource)
    (environment : Environment) (execute : Bool) (fuel : Nat)
    (fallthroughSite : ErrorSite) (fallthroughReason : ErrorReason)
    (statements : List StatementId) : Except Error StagedIntegerEvaluation :=
  evaluateStagedIntegerStatementsFuelWith id (rejectStagedIntegerCallsWith id)
    solved execute fuel source environment fallthroughSite fallthroughReason statements

def bindInputs (source : TypedSource) (seen : List Resolved.LocalId)
    (binders : List TypedBinder) (values : List Int) : Except Error Environment :=
  bindStagedIntegerInputsWith id source seen binders values

/-- The original input checks keep order and reject repeated binder identities.
Well-formed source binder extension is supplied independently from source typing. -/
inductive InputsChecked (source : TypedSource) : List Resolved.LocalId →
    List TypedBinder → List Int → Environment → Prop where
  | nil (seen : List Resolved.LocalId) : InputsChecked source seen [] [] []
  | cons {seen : List Resolved.LocalId} {binder : TypedBinder} {rest : List TypedBinder}
      {value : Int} {values : List Int} {environment : Environment}
      (owned : binder.id.owner = source.owner)
      (fresh : binder.id ∉ seen)
      (monomorphic : binder.scheme.quantified = [])
      (typed : binder.scheme.body = .integer)
      (tail : InputsChecked source (binder.id :: seen) rest values environment) :
      InputsChecked source seen (binder :: rest) (value :: values) (bind binder value :: environment)

inductive Checked (solved : List SolvedRequirement) (source : TypedSource) :
    Environment → Bool → Nat → List StatementId → StagedIntegerEvaluation → Prop where
  | letValue {environment : Environment} {execute : Bool} {fuel : Nat}
      {statement : StatementId} {rest : List StatementId} {node : StatementNode}
      {binder : TypedBinder} {initializer : ExpressionId} {initial result : StagedIntegerEvaluation}
      (found : source.lookupStatement? statement = some node)
      (form : node.form = .letDecl binder (some initializer))
      (nodeType : node.type = .unit)
      (fresh : environment.contains binder.id = false)
      (owned : binder.id.owner = source.owner)
      (monomorphic : binder.scheme.quantified = [])
      (binderType : binder.scheme.body = .integer)
      (initialChecked : IntegerChecked solved source environment execute fuel initializer initial)
      (bodyChecked : Checked solved source (bind binder initial.value :: environment) execute fuel rest result) :
      Checked solved source environment execute (fuel + 1) (statement :: rest)
        ⟨result.value, initial.consumedRequirements ++ result.consumedRequirements⟩
  | returnValue {environment : Environment} {execute : Bool} {fuel : Nat}
      {statement : StatementId} {node : StatementNode} {value : ExpressionId}
      {result : StagedIntegerEvaluation}
      (found : source.lookupStatement? statement = some node)
      (form : node.form = .returnStmt (some value))
      (nodeType : node.type = .integer)
      (valueChecked : IntegerChecked solved source environment execute fuel value result) :
      Checked solved source environment execute (fuel + 1) [statement] result
  | conditional {environment : Environment} {execute : Bool} {fuel : Nat}
      {statement : StatementId} {node : StatementNode} {condition : ExpressionId}
      {yes no : List StatementId} {guard : StagedBoolEvaluation}
      {left right : StagedIntegerEvaluation}
      (found : source.lookupStatement? statement = some node)
      (form : node.form = .ifThen condition yes (some no))
      (nodeType : node.type = .integer)
      (conditionChecked : BoolChecked solved source environment execute fuel condition guard)
      (thenChecked : Checked solved source environment (execute && guard.value) fuel yes left)
      (elseChecked : Checked solved source environment (execute && !guard.value) fuel no right) :
      Checked solved source environment execute (fuel + 1) [statement]
        ⟨if guard.value then left.value else right.value,
          guard.consumedRequirements ++ left.consumedRequirements ++ right.consumedRequirements⟩
  | block {environment : Environment} {execute : Bool} {fuel : Nat}
      {statement : StatementId} {node : StatementNode} {body : List StatementId}
      {result : StagedIntegerEvaluation}
      (found : source.lookupStatement? statement = some node)
      (form : node.form = .block body)
      (nodeType : node.type = .integer)
      (bodyChecked : Checked solved source environment execute fuel body result) :
      Checked solved source environment execute (fuel + 1) [statement] result

/-- Actual public function acceptance retains the complete source roots,
original binder order, and the successful ledger reconciliation. -/
inductive FunctionChecked (function : CheckedFunction) (arguments : List Int) (value : Int) : Prop where
  | intro {environment : Environment} {roots : List StatementId} {result : StagedIntegerEvaluation}
      (sourceOwned : function.typedBody.owner = function.declaration)
      (arity : function.typedBody.inputs.length = arguments.length)
      (inferredType : function.inferredBodyType = .integer)
      (functionType : function.type = .function
        (Ty.productMany (function.typedBody.inputs.map fun binder => binder.scheme.body)) .integer)
      (inputs : InputsChecked function.typedBody [] function.typedBody.inputs arguments environment)
      (rootsEq : roots.map NodeId.statement = function.typedBody.roots)
      (checked : Checked function.solvedRequirements function.typedBody environment true
        (function.typedBody.nodes.length + 1) roots result)
      (valueEq : result.value = value)
      (reconciled : reconcileConsumedRequirements function.declaration
        (function.solvedRequirements.map fun requirement => requirement.id) result.consumedRequirements = .ok []) :
      FunctionChecked function arguments value

end Solcore.Frontend.SourceCoreElaboration.Internal.Staged.Statements

namespace Solcore.Frontend.SourceCoreElaboration.Internal.Staged.Statements
open SourceInference TypeSystem
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

private theorem lookup_statement {source : TypedSource} {statement : StatementId} {node : StatementNode}
    (accepted : lookupStatement source statement = .ok node) :
    source.lookupStatement? statement = some node := by
  unfold lookupStatement at accepted
  split at accepted <;> simp_all [fail, TypedSource.lookupStatement?]

private theorem ensure_unit {site : ErrorSite} {type : Ty}
    (accepted : ensureTypeWith id site .unit type = .ok ()) : type = .unit := by
  unfold ensureTypeWith at accepted
  cases lowered : lowerType site type with
  | error reason => simp [lowered, Except.mapError, Bind.bind, Except.bind] at accepted
  | ok actual =>
    have same : actual = .unit := by
      by_cases same : actual = .unit
      · exact same
      · simp [lowered, Except.mapError, Bind.bind, Except.bind, same, failWith] at accepted
    subst actual
    cases type <;> simp_all [lowerType, fail, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
    case constructor head =>
      cases head with
      | declaration declaration => simp [lowerType, fail] at lowered
      | builtin builtin => cases builtin <;> simp_all [lowerType, fail, Ty.unit]
    case application function argument => split at lowered <;> contradiction
    case product left right =>
      cases leftEq : lowerType site left <;> simp only [leftEq] at lowered
      · cases lowered
      · cases rightEq : lowerType site right <;> simp [rightEq] at lowered

/-- Input acceptance retains the actual ordered compiler environment. -/
theorem inputs_checked {source : TypedSource} {seen : List Resolved.LocalId}
    {binders : List TypedBinder} {values : List Int} {environment : Environment}
    (accepted : bindInputs source seen binders values = .ok environment) :
    InputsChecked source seen binders values environment := by
  induction binders generalizing seen values environment with
  | nil =>
    cases values <;> simp_all [bindInputs, bindStagedIntegerInputsWith, failWith, pure, Pure.pure, Except.pure]
    exact .nil seen
  | cons binder rest ih =>
    cases values with
    | nil => simp [bindInputs, bindStagedIntegerInputsWith, failWith] at accepted
    | cons value values =>
      simp only [bindInputs, bindStagedIntegerInputsWith] at accepted
      have owned : binder.id.owner = source.owner := by
        by_cases owned : binder.id.owner = source.owner
        · exact owned
        · simp [owned, failWith] at accepted
      have fresh : binder.id ∉ seen := by
        by_cases fresh : binder.id ∈ seen
        · simp [owned, fresh, failWith] at accepted
        · exact fresh
      have monomorphic : binder.scheme.quantified = [] := by
        by_cases mono : binder.scheme.quantified = []
        · exact mono
        · simp [owned, fresh, mono, failWith] at accepted
      have typed : binder.scheme.body = .integer := by
        by_cases typed : binder.scheme.body = .integer
        · exact typed
        · simp [owned, fresh, monomorphic, typed, failWith] at accepted
      simp only [owned, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
        List.contains_eq_mem, fresh, decide_false, monomorphic, List.isEmpty_nil,
        Bool.not_true, typed] at accepted
      cases tailEq : bindStagedIntegerInputsWith id source (binder.id :: seen) rest values with
      | error reason => simp [tailEq, Bind.bind, Except.bind] at accepted
      | ok tail =>
        simp only [tailEq, Bind.bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
        subst environment
        exact .cons owned fresh monomorphic typed (ih tailEq)

end Solcore.Frontend.SourceCoreElaboration.Internal.Staged.Statements

namespace Solcore.Frontend.SourceCoreElaboration.Internal.Staged.Statements
open SourceInference TypeSystem
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

/-- The sole statement fuel proof retains validation of both branches and the
exact order in which the original evaluator consumes requirements. -/
theorem checked {solved : List SolvedRequirement} {source : TypedSource}
    {environment : Environment} {execute : Bool} {fuel : Nat}
    {fallthroughSite : ErrorSite} {fallthroughReason : ErrorReason}
    {statements : List StatementId} {result : StagedIntegerEvaluation}
    (accepted : evaluate solved source environment execute fuel fallthroughSite fallthroughReason statements = .ok result) :
    Checked solved source environment execute fuel statements result := by
  induction fuel generalizing environment execute fallthroughSite fallthroughReason statements result with
  | zero => cases statements <;> simp [evaluate, evaluateStagedIntegerStatementsFuelWith, failWith] at accepted
  | succ fuel ih =>
    cases statements with
    | nil => simp [evaluate, evaluateStagedIntegerStatementsFuelWith, failWith] at accepted
    | cons statement rest =>
      simp only [evaluate, evaluateStagedIntegerStatementsFuelWith] at accepted
      cases found : lookupStatement source statement with
      | error reason => simp [found, Except.mapError, Bind.bind, Except.bind] at accepted
      | ok node =>
        simp only [found, Except.mapError, id, Bind.bind, Except.bind] at accepted
        have found' := lookup_statement found
        cases form : node.form <;> simp only [form] at accepted
        all_goals try simp [failWith] at accepted
        case letDecl binder initializer =>
          cases validatedType : ensureTypeWith id (.occurrence statement.occurrence) .unit node.type with
          | error reason => simp [validatedType, Bind.bind, Except.bind] at accepted
          | ok checkedType =>
            cases checkedType
            simp only [validatedType, Bind.bind, Except.bind] at accepted
            have typed := ensure_unit validatedType
            have fresh : environment.contains binder.id = false := by
              cases fresh : environment.contains binder.id
              · rfl
              · simp [fresh, failWith] at accepted
            simp only [fresh, Bool.false_eq_true, ↓reduceIte] at accepted
            cases validated : validateStagedIntegerBinderWith id (.binder binder.id) source binder with
            | error reason => simp [validated, Bind.bind, Except.bind] at accepted
            | ok checkedBinder =>
              cases checkedBinder
              simp only [validated, Bind.bind, Except.bind] at accepted
              have facts := Staged.binder_checked validated
              cases initializer with
              | none => simp [failWith, Bind.bind, Except.bind] at accepted
              | some initializer =>
                simp only at accepted
                cases initialEq : evaluateStagedIntegerFuelWith id (rejectStagedIntegerCallsWith id)
                    solved source environment execute fuel initializer with
                | error reason => simp [initialEq, Bind.bind, Except.bind] at accepted
                | ok initial =>
                  simp only [initialEq, Bind.bind, Except.bind] at accepted
                  cases bodyEq : evaluateStagedIntegerStatementsFuelWith id (rejectStagedIntegerCallsWith id)
                      solved execute fuel source ({ binder, value := initial.value } :: environment)
                      fallthroughSite fallthroughReason rest with
                  | error reason => simp [bodyEq, Bind.bind, Except.bind] at accepted
                  | ok body =>
                    simp only [bodyEq, Bind.bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
                    subst result
                    exact .letValue found' form typed fresh facts.1 facts.2.1 facts.2.2
                      (integer_checked initialEq) (ih bodyEq)
        case returnStmt value =>
          have empty : rest = [] := by
            cases rest <;> simp_all [failWith]
          subst rest
          simp only [List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at accepted
          have typed : node.type = .integer := by
            by_cases typed : node.type = .integer
            · exact typed
            · simp [typed, failWith] at accepted
          simp only [typed, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at accepted
          cases value with
          | none => simp [failWith] at accepted
          | some value => exact .returnValue found' form typed (integer_checked accepted)
        case ifThen condition yes no =>
          have empty : rest = [] := by
            cases rest <;> simp_all [failWith]
          subst rest
          simp only [List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at accepted
          have typed : node.type = .integer := by
            by_cases typed : node.type = .integer
            · exact typed
            · simp [typed, failWith] at accepted
          simp only [typed, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at accepted
          cases no with
          | none => simp [failWith] at accepted
          | some no =>
            simp only at accepted
            cases guardEq : evaluateStagedBoolFuelWith id (rejectStagedIntegerCallsWith id)
                solved source environment execute fuel condition with
            | error reason => simp [guardEq, Bind.bind, Except.bind] at accepted
            | ok guard =>
              simp only [guardEq, Bind.bind, Except.bind] at accepted
              cases leftEq : evaluateStagedIntegerStatementsFuelWith id (rejectStagedIntegerCallsWith id)
                  solved (execute && guard.value) fuel source environment (.occurrence statement.occurrence)
                  (.conditionalBranchFallthrough .thenBranch) yes with
              | error reason => simp [leftEq, Bind.bind, Except.bind] at accepted
              | ok left =>
                simp only [leftEq, Bind.bind, Except.bind] at accepted
                cases rightEq : evaluateStagedIntegerStatementsFuelWith id (rejectStagedIntegerCallsWith id)
                    solved (execute && !guard.value) fuel source environment (.occurrence statement.occurrence)
                    (.conditionalBranchFallthrough .elseBranch) no with
                | error reason => simp [rightEq, Bind.bind, Except.bind] at accepted
                | ok right =>
                  simp only [rightEq, Bind.bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
                  subst result
                  simpa only [List.append_assoc] using
                    (Checked.conditional found' form typed (bool_checked guardEq) (ih leftEq) (ih rightEq))
        case block body =>
          have empty : rest = [] := by
            cases rest <;> simp_all [failWith]
          subst rest
          simp only [List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at accepted
          have typed : node.type = .integer := by
            by_cases typed : node.type = .integer
            · exact typed
            · simp [typed, failWith] at accepted
          simp only [typed, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at accepted
          exact .block found' form typed (ih accepted)

end Solcore.Frontend.SourceCoreElaboration.Internal.Staged.Statements

namespace Solcore.Frontend.SourceCoreElaboration.Internal.Staged.Statements
open SourceInference TypeSystem
set_option linter.unusedSimpArgs false

private theorem statement_roots {roots : List NodeId} {statements : List StatementId}
    (accepted : statementRoots roots = .ok statements) : statements.map NodeId.statement = roots := by
  induction roots generalizing statements with
  | nil => simp [statementRoots, pure, Pure.pure, Except.pure] at accepted; subst statements; rfl
  | cons head rest ih =>
    cases head with
    | expression expression => simp [statementRoots, fail] at accepted
    | statement statement =>
      simp only [statementRoots] at accepted
      cases tailEq : statementRoots rest with
      | error reason => simp [tailEq, Bind.bind, Except.bind] at accepted
      | ok tail =>
        simp only [tailEq, Bind.bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
        subst statements
        simp [ih tailEq]

/-- The public reject-calls function entry uses the same statement evaluator,
actual input binding, and successful complete ledger reconciliation. -/
theorem function_checked {function : CheckedFunction} {arguments : List Int} {value : Int}
    (accepted : evaluateStagedIntegerFunction function arguments = .ok value) :
    FunctionChecked function arguments value := by
  unfold evaluateStagedIntegerFunction evaluateStagedIntegerFunctionWith at accepted
  have owned : function.typedBody.owner = function.declaration := by
    by_cases owned : function.typedBody.owner = function.declaration
    · exact owned
    · simp [owned, failWith] at accepted
  have arity : function.typedBody.inputs.length = arguments.length := by
    by_cases arity : function.typedBody.inputs.length = arguments.length
    · exact arity
    · simp [owned, arity, failWith] at accepted
  simp only [owned, arity, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at accepted
  cases inputsEq : bindStagedIntegerInputsWith (fun error => error) function.typedBody [] function.typedBody.inputs arguments with
  | error reason => simp [inputsEq, Bind.bind, Except.bind] at accepted
  | ok environment =>
    simp only [inputsEq, Bind.bind, Except.bind] at accepted
    have inferred : function.inferredBodyType = .integer := by
      by_cases inferred : function.inferredBodyType = .integer
      · exact inferred
      · simp [inferred, failWith, Bind.bind, Except.bind] at accepted
    simp only [inferred, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, pure, Pure.pure, Except.pure,
      Bind.bind, Except.bind] at accepted
    have typed : function.type = .function
        (Ty.productMany (function.typedBody.inputs.map fun binder => binder.scheme.body)) .integer := by
      by_cases typed : function.type = .function
          (Ty.productMany (function.typedBody.inputs.map fun binder => binder.scheme.body)) .integer
      · exact typed
      · simp [typed, failWith, Bind.bind, Except.bind] at accepted
    simp only [typed, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, pure, Pure.pure, Except.pure,
      Bind.bind, Except.bind] at accepted
    cases rootsEq : statementRoots function.typedBody.roots with
    | error reason => simp [rootsEq, Except.mapError, Bind.bind, Except.bind] at accepted
    | ok roots =>
      simp only [rootsEq, Except.mapError, id, Bind.bind, Except.bind] at accepted
      cases evaluated : evaluateStagedIntegerStatementsFuelWith (fun error => error) rejectStagedIntegerCalls
          function.solvedRequirements true (function.typedBody.nodes.length + 1) function.typedBody environment
          (match finalStatement? roots with
            | some statement => .occurrence statement.occurrence
            | none => .declaration function.declaration)
          .statementListFallthrough roots with
      | error reason => simp [evaluated, Bind.bind, Except.bind] at accepted
      | ok result =>
        simp only [evaluated, Bind.bind, Except.bind] at accepted
        cases reconciled : reconcileConsumedRequirements function.declaration
            (function.solvedRequirements.map fun requirement => requirement.id) result.consumedRequirements with
        | error reason => simp [reconciled, Except.mapError, Bind.bind, Except.bind] at accepted
        | ok unconsumed =>
          simp only [reconciled, Except.mapError, id, Bind.bind, Except.bind] at accepted
          have empty : unconsumed = [] := by
            cases unconsumed <;> simp_all [failWith, Bind.bind, Except.bind]
          subst unconsumed
          simp only [List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            pure, Pure.pure, Except.pure, Bind.bind, Except.bind, Except.ok.injEq] at accepted
          exact .intro owned arity inferred typed (inputs_checked inputsEq) (statement_roots rootsEq)
            (checked evaluated) accepted reconciled

end Solcore.Frontend.SourceCoreElaboration.Internal.Staged.Statements
