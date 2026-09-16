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

/-- Lower one expression by following category-safe occurrence edges.  Fuel is
derived from the finite node table and turns malformed cyclic tables into a
located error. -/
private def lowerExpressionFuelWith {error : Type} (lift : Error → error)
    (onCall : CallElaborator error) (fuel : Nat) (source : TypedSource)
    (scope : Resolved.Context) (id : ExpressionId) :
    Except error LoweredExpression :=
  match fuel with
  | 0 => failWith lift (.occurrence id.occurrence) .expressionDepthLimit
  | fuel + 1 =>
    match (lookupExpression source id).mapError lift with
    | .error error => .error error
    | .ok node =>
        if !node.coercions.isEmpty then
          failWith lift (.occurrence id.occurrence)
            (.coercionsPresent node.coercions)
        else
          match node.form with
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
                    if !argumentNode.coercions.isEmpty then
                      failWith lift (.occurrence pair.2.occurrence)
                        (.coercionsPresent argumentNode.coercions)
                    else
                      ensureTypeWith lift (.occurrence pair.2.occurrence)
                        pair.1 argumentNode.type
                      lowerExpressionFuelWith lift onCall fuel source scope
                        pair.2
                let resolved ← plan.build
                  (loweredArguments.map fun argument => argument.resolved)
                pure {
                  resolved
                  consumedRequirements :=
                    loweredArguments.flatMap
                      (fun argument => argument.consumedRequirements) ++
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
                  | .group inner =>
                      lowerExpressionFuelWith lift onCall fuel source scope inner
                  | .tuple elements => do
                      let lowered ← elements.mapM fun element =>
                        lowerExpressionFuelWith lift onCall fuel source scope
                          element
                      pure {
                        resolved := productExpression
                          (lowered.map fun element => element.resolved)
                        consumedRequirements := lowered.flatMap
                          (fun element => element.consumedRequirements)
                      }
                  | .unary operator operand => do
                      let operand ←
                        lowerExpressionFuelWith lift onCall fuel source scope
                          operand
                      pure {
                        resolved := match operator with
                          | .logicalNot => .unary .boolNot operand.resolved
                          | .bitNot => .unary .wordNot operand.resolved
                        consumedRequirements := operand.consumedRequirements
                      }
                  | .binary left operator right => do
                      let left ←
                        lowerExpressionFuelWith lift onCall fuel source scope left
                      let right ←
                        lowerExpressionFuelWith lift onCall fuel source scope right
                      pure {
                        resolved := directBinary operator left.resolved
                          right.resolved
                        consumedRequirements := left.consumedRequirements ++
                          right.consumedRequirements
                      }
                  | .conditional condition thenBranch elseBranch => do
                      let condition ← lowerExpressionFuelWith lift onCall fuel
                        source scope condition
                      let thenBranch ← lowerExpressionFuelWith lift onCall fuel
                        source scope thenBranch
                      let elseBranch ← lowerExpressionFuelWith lift onCall fuel
                        source scope elseBranch
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

private def lowerExpressionAsWith {error : Type} (lift : Error → error)
    (onCall : CallElaborator error) (fuel : Nat) (source : TypedSource)
    (scope : Resolved.Context) (expected : Core.Ty) (id : ExpressionId) :
    Except error LoweredExpression := do
  let node ← (lookupExpression source id).mapError lift
  ensureTypeWith lift (.occurrence id.occurrence) expected node.type
  lowerExpressionFuelWith lift onCall fuel source scope id

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
    (onCall : CallElaborator error) :
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
                lowerExpressionAsWith lift onCall fuel source scope binderType
                  initializer
          let body ← lowerStatementsFuelWith lift onCall fuel source
            ((binder.id, binderType) :: scope) expected
            fallthroughSite fallthroughReason rest
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
              lowerExpressionAsWith lift onCall fuel source scope expected value
    | .ifThen condition thenBody elseBody => do
        if !rest.isEmpty then
          failWith lift site (.nonTailStatement .ifThen)
        else
          match elseBody with
          | none => failWith lift site .missingElseBranch
          | some elseBody => do
              ensureTypeWith lift site expected node.type
              let condition ← lowerExpressionAsWith lift onCall fuel source
                scope .bool condition
              let thenBranch ← lowerStatementsFuelWith lift onCall fuel source
                scope expected site (.conditionalBranchFallthrough .thenBranch)
                thenBody
              let elseBranch ← lowerStatementsFuelWith lift onCall fuel source
                scope expected site (.conditionalBranchFallthrough .elseBranch)
                elseBody
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
          lowerStatementsFuelWith lift onCall fuel source scope expected site
            .blockFallthrough body
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

private def eraseRequirement? (target : RequirementId) :
    List RequirementId → Option (List RequirementId)
  | [] => none
  | requirement :: rest =>
      if requirement = target then
        some rest
      else
        (eraseRequirement? target rest).map fun remaining =>
          requirement :: remaining

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
one caller-supplied policy handle otherwise staged call nodes.  All ordinary
typed-node, lexical-scope, coercion and requirement checks remain owned by this
module and are lifted into the consumer's error type. -/
def lowerFunctionBodyWith {error : Type} (lift : Error → error)
    (onCall : CallElaborator error) (function : CheckedFunction) :
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
    let lowered ← lowerStatementsFuelWith lift onCall
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
