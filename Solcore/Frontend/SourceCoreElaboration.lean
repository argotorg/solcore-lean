import Solcore.Frontend.ProgramChecking
import Solcore.Frontend.WordLiteral
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
  | proxy
  | index
  deriving Repr, BEq, DecidableEq

/-- Statement forms outside the tail-normal executable profile. -/
inductive UnsupportedStatement where
  | expression
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
  | stagedIntegerTypeMismatch (expected actual : Ty)
  | stagedIntegerExpressionNotClosed
  | stagedIntegerDepthLimit
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

/-- Validate the complete builtin `Int.fromInteger` contract before erasing it
to the runtime Word constant.  Expression and pattern carriers share this
primitive validation, including exact attachment and evidence checks. -/
private def lowerIntegerLiteralResolutionWith {error : Type}
    (lift : Error → error) (site : ErrorSite)
    (solvedRequirements : List SolvedRequirement) (nodeType : Ty)
    (attachedRequirements : List RequirementId)
    (source : Syntax.CoreLiteralValue)
    (resolution : IntegerLiteralResolution) :
    Except error LoweredExpression := do
  let validated ← validateIntegerLiteralResolutionWith lift site
    solvedRequirements nodeType attachedRequirements source resolution
    (.builtin .intWord)
    (fun target => ensureTypeWith lift site .word target)
  pure {
    resolved := .word (Core.Word.ofNatModulo validated.rawValue)
    consumedRequirements := validated.consumedRequirements
  }

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

private def StagedIntegerComparison.function :
    StagedIntegerComparison → BuiltinFunctionId
  | .eq => .integerEq
  | .lt => .integerLt

private def applyStagedIntegerComparison :
    StagedIntegerComparison → Int → Int → Bool
  | .eq, left, right => decide (left = right)
  | .lt, left, right => decide (left < right)

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

private def evaluateStagedIntegerFuelWith {error : Type}
    (lift : Error → error) (solvedRequirements : List SolvedRequirement)
    (source : TypedSource) :
    Nat → ExpressionId → Except error StagedIntegerEvaluation
  | 0, id =>
      failWith lift (.occurrence id.occurrence) .stagedIntegerDepthLimit
  | fuel + 1, id => do
      let node ← (lookupExpression source id).mapError lift
      let site := ErrorSite.occurrence id.occurrence
      match node.form with
      | .call callee arguments (.builtinFunction function) =>
          match stagedIntegerBinaryOperation? function with
          | some operation => do
              validateBuiltinFunctionCallWith lift source node callee arguments
                function
              match arguments with
              | [left, right] =>
                  let left ← evaluateStagedIntegerFuelWith lift
                    solvedRequirements source fuel left
                  let right ← evaluateStagedIntegerFuelWith lift
                    solvedRequirements source fuel right
                  pure {
                    value := applyStagedIntegerBinary operation left.value
                      right.value
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
          | .group inner =>
              if node.requirements.isEmpty then
                evaluateStagedIntegerFuelWith lift solvedRequirements source
                  fuel inner
              else
                failWith lift site (.requirementsPresent node.requirements)
          | _ =>
              failWith lift site .stagedIntegerExpressionNotClosed

/-- Evaluate exactly the closed staged-integer arithmetic fragment accepted by
runtime erasure.  The bound comes from the finite typed-node table, so malformed
cycles produce a located failure rather than nontermination. -/
def evaluateStagedInteger (solvedRequirements : List SolvedRequirement)
    (source : TypedSource) (id : ExpressionId) :
    Except Error StagedIntegerEvaluation :=
  evaluateStagedIntegerFuelWith (fun error => error) solvedRequirements source
    (source.nodes.length + 1) id

private def lowerWordFromIntegerWith {error : Type} (lift : Error → error)
    (solvedRequirements : List SolvedRequirement) (source : TypedSource)
    (fuel : Nat) (node : ExpressionNode) (callee : ExpressionId)
    (arguments : List ExpressionId) : Except error LoweredExpression := do
  validateBuiltinFunctionCallWith lift source node callee arguments
    .wordFromInteger
  match arguments with
  | [argument] =>
      let evaluated ← evaluateStagedIntegerFuelWith lift solvedRequirements
        source fuel argument
      pure {
        resolved := .word (Core.Word.ofIntModulo evaluated.value)
        consumedRequirements := evaluated.consumedRequirements
      }
  | _ =>
      failWith lift (.occurrence node.id.occurrence)
        (.builtinFunctionArgumentArityMismatch .wordFromInteger 1
          arguments.length)

private def lowerStagedIntegerComparisonWith {error : Type}
    (lift : Error → error)
    (solvedRequirements : List SolvedRequirement) (source : TypedSource)
    (fuel : Nat) (node : ExpressionNode) (callee : ExpressionId)
    (arguments : List ExpressionId) (comparison : StagedIntegerComparison) :
    Except error LoweredExpression := do
  let function := comparison.function
  validateBuiltinFunctionCallWith lift source node callee arguments function
  match arguments with
  | [left, right] =>
      let left ← evaluateStagedIntegerFuelWith lift solvedRequirements source
        fuel left
      let right ← evaluateStagedIntegerFuelWith lift solvedRequirements source
        fuel right
      pure {
        resolved := .bool
          (applyStagedIntegerComparison comparison left.value right.value)
        consumedRequirements := left.consumedRequirements ++
          right.consumedRequirements
      }
  | _ =>
      failWith lift (.occurrence node.id.occurrence)
        (.builtinFunctionArgumentArityMismatch function 2 arguments.length)

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

/-- Lower one coercion-cleared expression node.  Recursive edges return to the
outer traversal, so every child independently receives its own coercion policy
without reapplying the current node's path. -/
private def lowerExpressionNodeWith {error : Type} (lift : Error → error)
    (onCall : CallElaborator error)
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
      let plan ← onCall scope node callee arguments resolution
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
          | .proxy _ => failWith lift (.occurrence id.occurrence)
              (.unsupportedExpression .proxy)
          | .index _ _ => failWith lift (.occurrence id.occurrence)
              (.unsupportedExpression .index)

/-- Lower one expression by following category-safe occurrence edges.  Fuel is
derived from the finite node table and turns malformed cyclic tables into a
located error.  A nonempty coercion path is checked and planned once around a
coercion-cleared view of the base node. -/
private def lowerExpressionFuelWith {error : Type} (lift : Error → error)
    (onCall : CallElaborator error)
    (onRequiredUnary : RequiredUnaryElaborator error)
    (onRequiredBinary : RequiredBinaryElaborator error)
    (onCoercion : CoercionElaborator error)
    (solvedRequirements : List SolvedRequirement)
    (fuel : Nat) (source : TypedSource) (scope : Resolved.Context)
    (id : ExpressionId) :
    Except error LoweredExpression :=
  match fuel with
  | 0 => failWith lift (.occurrence id.occurrence) .expressionDepthLimit
  | fuel + 1 => do
      let node ← (lookupExpression source id).mapError lift
      let recurse := lowerExpressionFuelWith lift onCall onRequiredUnary
        onRequiredBinary onCoercion solvedRequirements fuel source scope
      match node.form with
      | .call callee arguments (.builtinFunction .wordFromInteger) =>
          lowerWordFromIntegerWith lift solvedRequirements source fuel node
            callee arguments
      | .call callee arguments (.builtinFunction .integerEq) =>
          lowerStagedIntegerComparisonWith lift solvedRequirements source fuel
            node callee arguments .eq
      | .call callee arguments (.builtinFunction .integerLt) =>
          lowerStagedIntegerComparisonWith lift solvedRequirements source fuel
            node callee arguments .lt
      | _ =>
          match node.coercions with
          | [] =>
              lowerExpressionNodeWith lift onCall onRequiredUnary
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
              let base ← lowerExpressionNodeWith lift onCall onRequiredUnary
                onRequiredBinary solvedRequirements source scope recurse baseNode
              applyCoercionPlans base.resolved base.consumedRequirements plans

private def lowerExpressionAsWith {error : Type} (lift : Error → error)
    (onCall : CallElaborator error)
    (onRequiredUnary : RequiredUnaryElaborator error)
    (onRequiredBinary : RequiredBinaryElaborator error)
    (onCoercion : CoercionElaborator error)
    (solvedRequirements : List SolvedRequirement)
    (fuel : Nat) (source : TypedSource) (scope : Resolved.Context)
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
  lowerExpressionFuelWith lift onCall onRequiredUnary onRequiredBinary
    onCoercion solvedRequirements fuel source scope id

private inductive MatchPatternLeaf where
  | wildcard
  | integerLiteral (literal : Syntax.CoreLiteral)

private def matchPatternLeaf : MatchPatternSource → MatchPatternLeaf
  | .wildcard _ _ => .wildcard
  | .integerLiteral _ literal => .integerLiteral literal
  | .group _ inner => matchPatternLeaf inner

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
    (onCall : CallElaborator error)
    (onRequiredUnary : RequiredUnaryElaborator error)
    (onRequiredBinary : RequiredBinaryElaborator error)
    (onCoercion : CoercionElaborator error)
    (solvedRequirements : List SolvedRequirement) :
    Nat → TypedSource → Resolved.Context → Core.Ty → ErrorSite →
      ErrorReason → List StatementId → Except error LoweredExpression
  | _, _, _, _, fallthroughSite, fallthroughReason, [] =>
      failWith lift fallthroughSite fallthroughReason
  | 0, _, _, _, _, _, id :: _ =>
      failWith lift (.occurrence id.occurrence) .statementDepthLimit
  | fuel + 1, source, scope, expected, fallthroughSite, fallthroughReason,
      id :: rest => do
    let node ← (lookupStatement source id).mapError lift
    let site := ErrorSite.occurrence id.occurrence
    match node.form with
    | .letDecl binder initializer => do
        ensureTypeWith lift site .unit node.type
        if scope.ids.contains binder.id then
          failWith lift (.binder binder.id) (.duplicateLocal binder.id)
        else if !binder.scheme.quantified.isEmpty then
          failWith lift (.binder binder.id)
            (.polymorphicLocal binder.scheme.quantified)
        else
          let binderType ← (lowerType (.binder binder.id)
            binder.scheme.body).mapError lift
          let initializer ← match initializer with
            | none => failWith lift site .uninitializedLet
            | some initializer =>
                lowerExpressionAsWith lift onCall onRequiredUnary
                  onRequiredBinary onCoercion solvedRequirements fuel source
                  scope binderType initializer
          let body ← lowerStatementsFuelWith lift onCall onRequiredUnary
            onRequiredBinary onCoercion solvedRequirements fuel source
            ((binder.id, binderType) :: scope) expected fallthroughSite
            fallthroughReason rest
          pure {
            resolved := .letE binder.id initializer.resolved body.resolved
            consumedRequirements := initializer.consumedRequirements ++
              body.consumedRequirements
          }
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
              lowerExpressionAsWith lift onCall onRequiredUnary
                onRequiredBinary onCoercion solvedRequirements fuel source
                scope expected value
    | .ifThen condition thenBody elseBody => do
        if !rest.isEmpty then
          failWith lift site (.nonTailStatement .ifThen)
        else
          match elseBody with
          | none => failWith lift site .missingElseBranch
          | some elseBody => do
              ensureTypeWith lift site expected node.type
              let condition ← lowerExpressionAsWith lift onCall
                onRequiredUnary onRequiredBinary onCoercion solvedRequirements
                fuel source scope .bool condition
              let thenBranch ← lowerStatementsFuelWith lift onCall
                onRequiredUnary onRequiredBinary onCoercion solvedRequirements
                fuel source scope expected site
                (.conditionalBranchFallthrough .thenBranch) thenBody
              let elseBranch ← lowerStatementsFuelWith lift onCall
                onRequiredUnary onRequiredBinary onCoercion solvedRequirements
                fuel source scope expected site
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
          lowerStatementsFuelWith lift onCall onRequiredUnary onRequiredBinary
            onCoercion solvedRequirements fuel source scope expected site
            .blockFallthrough body
    | .matchWith resolution => do
        if !rest.isEmpty then
          failWith lift site (.nonTailStatement .matchWith)
        else if resolution.hiddenScrutinee.owner != source.owner then
          failWith lift site (.matchHiddenOwnerMismatch source.owner
            resolution.hiddenScrutinee.owner)
        else if scope.ids.contains resolution.hiddenScrutinee then
          failWith lift site (.duplicateMatchHidden
            resolution.hiddenScrutinee)
        else
          ensureTypeWith lift site expected node.type
          let scrutineeNode ←
            (lookupExpression source resolution.scrutinee).mapError lift
          let scrutineeCoreType ←
            (lowerType (.occurrence resolution.scrutinee.occurrence)
              scrutineeNode.type).mapError lift
          let scrutinee ← lowerExpressionAsWith lift onCall onRequiredUnary
            onRequiredBinary onCoercion solvedRequirements fuel source scope
            scrutineeCoreType resolution.scrutinee
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
                onRequiredUnary onRequiredBinary onCoercion solvedRequirements
                fuel source scope expected site .blockFallthrough arm.body
              pure { pattern, branch }
            let fallback ← match resolution.defaultBody with
              | none => pure none
              | some body => do
                  let lowered ← lowerStatementsFuelWith lift onCall
                    onRequiredUnary onRequiredBinary onCoercion
                    solvedRequirements fuel source scope expected site
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

/-- Lower a checked function body to the resolved local fragment while letting
caller-supplied policies handle otherwise staged calls, requirement-bearing
unary and binary expressions, and coercion steps.  All child traversal,
typed-node, lexical-scope, coercion-path, and requirement checks remain owned by
this module and are lifted into the consumer's error type. -/
def lowerFunctionBodyWithRuntimePolicies {error : Type} (lift : Error → error)
    (onCall : CallElaborator error)
    (onRequiredUnary : RequiredUnaryElaborator error)
    (onRequiredBinary : RequiredBinaryElaborator error)
    (onCoercion : CoercionElaborator error)
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
    let lowered ← lowerStatementsFuelWith lift onCall onRequiredUnary
      onRequiredBinary onCoercion function.solvedRequirements
      (source.nodes.length + 1) source inputs expected fallthroughSite
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
