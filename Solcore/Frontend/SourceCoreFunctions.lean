import Solcore.Frontend.SourceCoreFunctionTypes
import Solcore.Frontend.SourceCoreCalls

/-! Monomorphic function values over shared optional cells. Named references
carry a deterministic plan-local identity; lambdas retain anonymous identity
and capture the existing cell references. A supplied statement compiler owns
control flow, so this module adds no source evaluator or duplicate loop logic.
Ordinary let initializers are still evaluated before their binding is allocated. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreFunctions

open SourceInference

abbrev Context := SourceCoreCalls.Context
abbrev Scope := SourceCoreBasic.Scope
abbrev Error := SourceCoreBasic.Error
abbrev LoweredExpr := SourceCoreBasic.LoweredExpr
abbrev Signature := SourceCoreCalls.Signature
abbrev Key := SourceCoreCalls.Key

abbrev ExpressionLowerer := Nat → TypedSource → Scope → ExpressionId →
  (ExpressionId → Core.Word) → Except Error LoweredExpr

/-- The callback receives this expression policy for lambda bodies. It must
use the function-value binder, assignment, and statement type projection. -/
abbrev BodyLowerer := ExpressionLowerer → Nat → TypedSource → Scope → List StatementId →
  Core.Ty → (ExpressionId → Core.Word) → Core.Word → Core.Word → Except Error Core.Expr

private def globalAt (globals : List Signature) (key : Key) : Except Error (Nat × Signature) :=
  match globals.zipIdx.filter (fun entry => decide (entry.1.key = key)) with
  | [] => .error (.callPreparation (.missingSpecialization key))
  | [(signature, index)] => .ok (index, signature)
  | candidates => .error (.callPreparation (.duplicateSpecialization key candidates.length))

private def selectedSignature (context : Context) (source : TypedSource) (node : ExpressionNode)
    (instantiation : DeclarationInstantiation) (isReference : Bool) : Except Error (Nat × Signature) := do
  if source.owner ≠ context.owner.declaration then throw (.ownerMismatch context.owner.declaration source.owner)
  let caller ← (SourceCompilationPlan.exactSpecialization context.plan context.owner).mapError SourceCoreBasic.Error.callPreparation
  unless caller.assumptions.isEmpty do throw (.callPreparation (.unresolvedAssumptions context.owner caller.assumptions))
  let target ← (SourceCompilationPlan.exactInstantiationKey context.plan instantiation).mapError SourceCoreBasic.Error.callPreparation
  let key ← (if isReference then SourceCompilationPlan.exactReferenceKey context.plan context.owner node.id target
    else SourceCompilationPlan.exactCallKey context.plan context.owner node.id target).mapError SourceCoreBasic.Error.callPreparation
  let specialized ← (SourceCompilationPlan.exactSpecialization context.plan key).mapError SourceCoreBasic.Error.callPreparation
  unless specialized.assumptions.isEmpty do throw (.callPreparation (.unresolvedAssumptions key specialized.assumptions))
  if specialized.function.returnComptime || specialized.function.typedBody.inputs.any (·.comptime) then
    throw (.unsupportedExpression node.id node.form)
  let (parameter, result) ← match specialized.function.type with
    | .function parameter result => pure (parameter, result)
    | _ => .error (.callPreparation (.invalidFunctionType key specialized.function.type))
  let site := SourceCoreElaboration.ErrorSite.occurrence node.id.occurrence
  let parameterType ← SourceCoreFunctionTypes.projectType site parameter
  let resultType ← SourceCoreFunctionTypes.projectType site result
  let (index, signature) ← globalAt context.globals key
  SourceCoreBasic.ensureType site parameterType signature.parameterType
  SourceCoreBasic.ensureType site resultType signature.resultType
  pure (index, signature)

def namedReference (signature : Signature) (index : Nat) (identity internalReason : Core.Word) : Core.Expr :=
  Core.LanguageResult.bind (Core.TaggedFunction.functionType signature.parameterType signature.resultType)
    (Core.OptionalCell.read signature.functionType (.var index) internalReason)
    (Core.LanguageResult.success (Core.TaggedFunction.identified identity (.var 0)))

theorem namedReference_hasType {definitions : Core.DataEnvironment} {environment : Core.Context}
    {signature : Signature} {index : Nat} (identity internalReason : Core.Word)
    (parameterWF : Core.Ty.WellFormed definitions signature.parameterType)
    (resultWF : Core.Ty.WellFormed definitions signature.resultType)
    (reference : environment[index]? = some signature.referenceType) :
    Core.HasType environment (namedReference signature index identity internalReason)
      (Core.LanguageResult.resultType
        (Core.TaggedFunction.functionType signature.parameterType signature.resultType)) definitions := by
  apply Core.LanguageResult.bind_hasType (Core.TaggedFunction.functionType_wellFormed parameterWF resultWF)
  · apply Core.OptionalCell.read_hasType internalReason
      (.function parameterWF (Core.LanguageResult.resultType_wellFormed resultWF))
    exact .var reference
  · exact Core.LanguageResult.success_hasType (Core.TaggedFunction.identified_hasType identity (.var rfl))

/-- Parameter projections follow Unit/single/right-product source packing. -/
def argumentProjection (index : Nat) : Nat → Core.Expr → Core.Expr
  | 0, _ => .unit
  | 1, bundle => bundle
  | count + 2, bundle =>
      if index = 0 then .first bundle else argumentProjection (index - 1) (count + 1) (.second bundle)

def bindParameters (parameters : List (TypedBinder × Core.Ty)) (resultType : Core.Ty) (body : Core.Expr) : Core.Expr :=
  parameters.zipIdx.foldr (fun ((_, type), index) continuation =>
    Core.LocalSequence.letInitialized resultType type
      (Core.LanguageResult.success (argumentProjection index parameters.length (.var index))) continuation) body

private def lambdaParameters (source : TypedSource) : Scope → List TypedBinder →
    Except Error (List (TypedBinder × Core.Ty) × Scope)
  | scope, [] => pure ([], scope)
  | scope, parameter :: parameters => do
      let type ← SourceCoreFunctionTypes.lowerBinder source scope parameter
      let (remaining, scope) ← lambdaParameters source ((parameter.id, type) :: scope) parameters
      pure ((parameter, type) :: remaining, scope)

/-- All recursive expression budgets are bounded by the current remaining
budget, including callbacks from the separately supplied statement traversal. -/
def lowerExpressionWithReasons (lowerBody : BodyLowerer) : Nat → Context → TypedSource → Scope → ExpressionId →
    (ExpressionId → Core.Word) → Except Error LoweredExpr
  | 0, _, _, _, id, _ => .error (.traversalExhausted (.occurrence id.occurrence))
  | fuel + 1, context, source, scope, id, reasonAt => do
      if id.occurrence.owner ≠ source.owner then throw (.ownerMismatch source.owner id.occurrence.owner)
      let node ← match source.lookupExpression? id with
        | some node => pure node
        | none => .error (.missingExpression id)
      match node.form with
      | .integerLiteral literal resolution =>
          let validated ← (SourceCoreElaboration.validateWordIntegerLiteral context.solvedRequirements
            node literal resolution).mapError SourceCoreBasic.Error.literalEvidence
          pure ⟨.word, Core.LanguageResult.success (.word validated.value)⟩
      | _ =>
          let (node, type) ← SourceCoreFunctionTypes.readExpression source id
          let site := SourceCoreElaboration.ErrorSite.occurrence id.occurrence
          match node.form with
          | .reference _ (.local _) =>
              let read ← SourceCoreFunctionTypes.lowerRead source scope id (reasonAt id)
              pure ⟨type, read⟩
          | .reference _ (.declaration instantiation) =>
              let (index, signature) ← selectedSignature context source node instantiation true
              SourceCoreBasic.ensureType site type (Core.TaggedFunction.functionType signature.parameterType signature.resultType)
              let identity ← match Core.Word.ofNat? (index + 1) with
                | some identity => pure identity
                | none => .error (.unsupportedExpression id node.form)
              pure ⟨type, namedReference signature (scope.length + context.administrativePrefix + index)
                identity context.internalReason⟩
          | .call callee arguments (.declaration instantiation) =>
              if callee.occurrence.owner ≠ source.owner then throw (.ownerMismatch source.owner callee.occurrence.owner)
              discard <| SourceCoreFunctionTypes.readExpression source callee
              (SourceCompilationPlan.validateDirectDeclarationCallee source id callee instantiation).mapError SourceCoreBasic.Error.callPreparation
              let (index, signature) ← selectedSignature context source node instantiation false
              let specialized ← (SourceCompilationPlan.exactSpecialization context.plan signature.key).mapError SourceCoreBasic.Error.callPreparation
              if arguments.length ≠ specialized.function.typedBody.inputs.length then
                throw (.callPreparation (.argumentArityMismatch specialized.function.typedBody.inputs.length arguments.length))
              SourceCoreBasic.ensureType site signature.resultType type
              let lowered ← arguments.mapM fun argument =>
                lowerExpressionWithReasons lowerBody fuel context source scope argument reasonAt
              let packed := SourceCoreCalls.packArguments lowered
              SourceCoreBasic.ensureType site signature.parameterType packed.type
              pure ⟨type, SourceCoreCalls.call signature (scope.length + context.administrativePrefix + index)
                packed.expression context.internalReason⟩
          | .call callee arguments (.indirect metadata) =>
              unless metadata.argumentCoercions.isEmpty do throw (.unsupportedExpression id node.form)
              (SourceCompilationPlan.validateIndirectCallMetadata source node callee arguments metadata).mapError SourceCoreBasic.Error.callPreparation
              let (calleeNode, _) ← SourceCoreFunctionTypes.readExpression source callee
              let (parameter, result) ← match calleeNode.type with
                | .function parameter result => pure (parameter, result)
                | _ => .error (.callPreparation (.indirectCalleeNotFunction id calleeNode.type))
              let parameterType ← SourceCoreFunctionTypes.projectType site parameter
              let resultType ← SourceCoreFunctionTypes.projectType site result
              SourceCoreBasic.ensureType site resultType type
              let callee ← lowerExpressionWithReasons lowerBody fuel context source scope callee reasonAt
              let lowered ← arguments.mapM fun argument =>
                lowerExpressionWithReasons lowerBody fuel context source scope argument reasonAt
              let packed := SourceCoreCalls.packArguments lowered
              SourceCoreBasic.ensureType site parameterType packed.type
              SourceCoreBasic.ensureType site (Core.TaggedFunction.functionType parameterType resultType) callee.type
              pure ⟨type, Core.TaggedFunction.call resultType callee.expression packed.expression⟩
          | .lambda parameters returnType statements =>
              let (parameterType, resultType) ← match node.type with
                | .function parameter result => pure (parameter, result)
                | _ => .error (.unsupportedExpression id node.form)
              let bundle := TypeSystem.Ty.productMany (parameters.map (·.scheme.body))
              if bundle ≠ parameterType then throw (.callPreparation (.typeMismatch parameterType (some bundle)))
              if returnType ≠ resultType then throw (.callPreparation (.resultTypeMismatch resultType (some returnType)))
              let parameterCore ← SourceCoreFunctionTypes.projectType site parameterType
              let resultCore ← SourceCoreFunctionTypes.projectType site resultType
              let (parameters, bodyScope) ← lambdaParameters source scope parameters
              let body ← lowerBody
                (fun budget childSource childScope childId childReasonAt =>
                  lowerExpressionWithReasons lowerBody (min budget fuel) context childSource childScope childId childReasonAt)
                fuel source bodyScope statements resultCore reasonAt context.internalReason context.internalReason
              let rawBody := bindParameters parameters resultCore (body.weakenAt parameters.length)
              pure ⟨type, Core.LanguageResult.success (Core.TaggedFunction.anonymous
                (.lambda parameterCore (Core.LanguageResult.resultType resultCore) rawBody))⟩
          | .unary operator operand =>
              let operand ← lowerExpressionWithReasons lowerBody fuel context source scope operand reasonAt
              let coreOperator := SourceCorePrimitive.unaryOperator operator
              SourceCoreBasic.ensureType site coreOperator.operandType operand.type
              SourceCoreBasic.ensureType site coreOperator.resultType type
              pure ⟨type, Core.LocalPrimitiveResults.unary coreOperator operand.expression⟩
          | .binary left operator right =>
              let left ← lowerExpressionWithReasons lowerBody fuel context source scope left reasonAt
              let right ← lowerExpressionWithReasons lowerBody fuel context source scope right reasonAt
              SourceCoreBasic.ensureType site (SourceCorePrimitive.binaryOperandType operator) left.type
              SourceCoreBasic.ensureType site (SourceCorePrimitive.binaryOperandType operator) right.type
              SourceCoreBasic.ensureType site (SourceCorePrimitive.binaryResultType operator) type
              pure ⟨type, SourceCorePrimitive.binary operator left.expression right.expression⟩
          | .conditional condition thenBranch elseBranch =>
              let condition ← lowerExpressionWithReasons lowerBody fuel context source scope condition reasonAt
              SourceCoreBasic.ensureType site .bool condition.type
              let thenBranch ← lowerExpressionWithReasons lowerBody fuel context source scope thenBranch reasonAt
              let elseBranch ← lowerExpressionWithReasons lowerBody fuel context source scope elseBranch reasonAt
              SourceCoreBasic.ensureType site type thenBranch.type
              SourceCoreBasic.ensureType site type elseBranch.type
              pure ⟨type, Core.LocalControl.choose type condition.expression thenBranch.expression elseBranch.expression⟩
          | .group inner =>
              let inner ← lowerExpressionWithReasons lowerBody fuel context source scope inner reasonAt
              SourceCoreBasic.ensureType site type inner.type
              pure inner
          | .tuple [left, right] =>
              let left ← lowerExpressionWithReasons lowerBody fuel context source scope left reasonAt
              let right ← lowerExpressionWithReasons lowerBody fuel context source scope right reasonAt
              SourceCoreBasic.ensureType site type (.product left.type right.type)
              pure ⟨type, Core.LocalSequence.pair left.type right.type left.expression right.expression⟩
          | _ => SourceCoreBasic.lowerExpression (fuel + 1) source scope id (reasonAt id)
termination_by fuel => fuel

end Solcore.Frontend.SourceCoreFunctions
