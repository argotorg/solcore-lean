import Solcore.Frontend.SourceCorePrimitive
import Solcore.Frontend.SourceCompilationPlan

/-! Monomorphic named calls through ordinary optional Core function cells.
Arguments run in source order before the selected cell is read. Global cells
are supplied by the enclosing program installation, after local references and
any administrative binders. The prepared plan authenticates occurrence edges;
this fragment does not execute source code or lower evidence-bearing methods. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreCalls

open SourceInference

abbrev Key := SourceSpecialization.SpecializationKey
abbrev Plan := SourceSpecializationWorklist.Plan
abbrev Scope := SourceCoreBasic.Scope
abbrev LoweredExpr := SourceCoreBasic.LoweredExpr

structure Signature where
  key : Key
  parameterType : Core.Ty
  resultType : Core.Ty
  deriving Repr, DecidableEq

structure Context where
  plan : Plan
  owner : Key
  /-- Newest-first, in the same order as the enclosing Core environment. -/
  globals : List Signature
  administrativePrefix : Nat
  solvedRequirements : List SolvedRequirement
  internalReason : Core.Word
  deriving Repr

abbrev Error := SourceCoreBasic.Error

/-- A function returns a language result, including on a recursive call. -/
def Signature.functionType (signature : Signature) : Core.Ty :=
  .function signature.parameterType (Core.LanguageResult.resultType signature.resultType)

def Signature.referenceType (signature : Signature) : Core.Ty :=
  Core.OptionalCell.referenceType signature.functionType

/-- Source argument packing: no arguments form Unit; one is unchanged;
multiple arguments form a right-associated product, with left-to-right effects. -/
def packArguments : List LoweredExpr → LoweredExpr
  | [] => ⟨.unit, Core.LanguageResult.success .unit⟩
  | [argument] => argument
  | argument :: rest =>
      let tail := packArguments rest
      ⟨.product argument.type tail.type,
        Core.LocalSequence.pair argument.type tail.type argument.expression tail.expression⟩

/-- Read the global cell only after the argument bundle succeeds. The argument
and function payload binders are private to this expression. -/
def call (signature : Signature) (index : Nat) (arguments : Core.Expr)
    (internalReason : Core.Word) : Core.Expr :=
  Core.LanguageResult.bind signature.resultType arguments
    (Core.LanguageResult.bind signature.resultType
      (Core.OptionalCell.read signature.functionType (.var (index + 1)) internalReason)
      (.apply (.var 0) (.var 1)))

theorem call_hasType {definitions : Core.DataEnvironment} {environment : Core.Context}
    {signature : Signature} {index : Nat} {arguments : Core.Expr}
    (internalReason : Core.Word)
    (parameterWF : Core.Ty.WellFormed definitions signature.parameterType)
    (resultWF : Core.Ty.WellFormed definitions signature.resultType)
    (reference : environment[index]? = some signature.referenceType)
    (argumentsTyped : Core.HasType environment arguments
      (Core.LanguageResult.resultType signature.parameterType) definitions) :
    Core.HasType environment (call signature index arguments internalReason)
      (Core.LanguageResult.resultType signature.resultType) definitions := by
  apply Core.LanguageResult.bind_hasType resultWF argumentsTyped
  apply Core.LanguageResult.bind_hasType resultWF
  · apply Core.OptionalCell.read_hasType internalReason
      (.function parameterWF (Core.LanguageResult.resultType_wellFormed resultWF))
    exact .var (by simpa [Signature.referenceType, Signature.functionType] using reference)
  · exact .apply (.var rfl) (.var rfl)

theorem call_argument_failure {environment : Core.Environment} {before after : Core.Store}
    {signature : Signature} {index : Nat} {arguments : Core.Expr}
    {reason internalReason : Core.Word}
    (evaluation : Core.Evaluates environment before arguments
      (.inLeft signature.parameterType (.word reason)) after) :
    Core.Evaluates environment before (call signature index arguments internalReason)
      (.inLeft signature.resultType (.word reason)) after :=
  Core.LanguageResult.bind_failure signature.resultType evaluation

theorem call_global_failure {environment : Core.Environment} {before middle after : Core.Store}
    {signature : Signature} {index : Nat} {arguments : Core.Expr}
    {argument : Core.Value} {reason internalReason : Core.Word}
    (argumentsEvaluation : Core.Evaluates environment before arguments
      (.inRight .word argument) middle)
    (globalEvaluation : Core.Evaluates (argument :: environment) middle
      (Core.OptionalCell.read signature.functionType (.var (index + 1)) internalReason)
      (.inLeft signature.functionType (.word reason)) after) :
    Core.Evaluates environment before (call signature index arguments internalReason)
      (.inLeft signature.resultType (.word reason)) after :=
  Core.LanguageResult.bind_success signature.resultType argumentsEvaluation
    (Core.LanguageResult.bind_failure signature.resultType globalEvaluation)

theorem call_success {environment captured : Core.Environment}
    {before middle applied after : Core.Store}
    {signature : Signature} {index : Nat} {arguments body : Core.Expr}
    {argument result : Core.Value} {internalReason : Core.Word}
    (argumentsEvaluation : Core.Evaluates environment before arguments
      (.inRight .word argument) middle)
    (globalEvaluation : Core.Evaluates (argument :: environment) middle
      (Core.OptionalCell.read signature.functionType (.var (index + 1)) internalReason)
      (.inRight .word (.closure signature.parameterType
        (Core.LanguageResult.resultType signature.resultType) body captured)) applied)
    (bodyEvaluation : Core.Evaluates (argument :: captured) applied body result after) :
    Core.Evaluates environment before (call signature index arguments internalReason) result after :=
  Core.LanguageResult.bind_success signature.resultType argumentsEvaluation
    (Core.LanguageResult.bind_success signature.resultType globalEvaluation
      (.apply (.var rfl) (.var rfl) bodyEvaluation))

private def globalAt (globals : List Signature) (key : Key) :
    Except Error (Nat × Signature) :=
  match globals.zipIdx.filter (fun entry => decide (entry.1.key = key)) with
  | [] => .error (.callPreparation (.missingSpecialization key))
  | [(signature, index)] => .ok (index, signature)
  | candidates => .error (.callPreparation (.duplicateSpecialization key candidates.length))

/-- Validate a direct edge and its projected signature before compiling its
arguments. No assumption dictionary or staged result is implemented here. -/
def directSignature (context : Context) (source : TypedSource)
    (node : ExpressionNode) (callee : ExpressionId) (arguments : List ExpressionId)
    (instantiation : DeclarationInstantiation) : Except Error (Nat × Signature) := do
  if source.owner ≠ context.owner.declaration then
    throw (.ownerMismatch context.owner.declaration source.owner)
  let caller ← (SourceCompilationPlan.exactSpecialization context.plan context.owner).mapError SourceCoreBasic.Error.callPreparation
  unless caller.assumptions.isEmpty do throw (.callPreparation (.unresolvedAssumptions context.owner caller.assumptions))
  if callee.occurrence.owner ≠ source.owner then
    throw (.ownerMismatch source.owner callee.occurrence.owner)
  let calleeNode ← (SourceCompilationPlan.exactExpression source callee).mapError SourceCoreBasic.Error.callPreparation
  unless calleeNode.requirements.isEmpty do throw (.requirementsPresent callee)
  unless calleeNode.coercions.isEmpty do throw (.coercionsPresent callee)
  (SourceCompilationPlan.validateDirectDeclarationCallee source node.id callee instantiation).mapError SourceCoreBasic.Error.callPreparation
  let target ← (SourceCompilationPlan.exactInstantiationKey context.plan instantiation).mapError SourceCoreBasic.Error.callPreparation
  let key ← (SourceCompilationPlan.exactCallKey context.plan context.owner node.id target).mapError SourceCoreBasic.Error.callPreparation
  let specialized ← (SourceCompilationPlan.exactSpecialization context.plan key).mapError SourceCoreBasic.Error.callPreparation
  unless specialized.assumptions.isEmpty do throw (.callPreparation (.unresolvedAssumptions key specialized.assumptions))
  if specialized.function.returnComptime || specialized.function.typedBody.inputs.any (·.comptime) then
    throw (.unsupportedExpression node.id node.form)
  if arguments.length ≠ specialized.function.typedBody.inputs.length then
    throw (.callPreparation (.argumentArityMismatch specialized.function.typedBody.inputs.length arguments.length))
  let (parameter, result) ← match specialized.function.type with
    | .function parameter result => pure (parameter, result)
    | _ => .error (.callPreparation (.invalidFunctionType key specialized.function.type))
  let site := SourceCoreElaboration.ErrorSite.occurrence node.id.occurrence
  let parameterType ← (SourceCoreBasic.projectType site parameter)
  let resultType ← (SourceCoreBasic.projectType site result)
  let (index, signature) ← globalAt context.globals key
  (SourceCoreBasic.ensureType site parameterType signature.parameterType)
  (SourceCoreBasic.ensureType site resultType signature.resultType)
  pure (index, signature)

/-- The same policy recurses into every supported composite expression, so
calls retain primitive short circuit and local-read diagnostic providers. -/
def lowerExpressionWithReasons : Nat → Context → TypedSource → Scope → ExpressionId →
    (ExpressionId → Core.Word) → Except Error LoweredExpr
  | 0, _, _, _, id, _ => .error (.traversalExhausted (.occurrence id.occurrence))
  | fuel + 1, context, source, scope, id, reasonAt => do
      if id.occurrence.owner ≠ source.owner then
        throw (.ownerMismatch source.owner id.occurrence.owner)
      let node ← match source.lookupExpression? id with
        | some node => pure node
        | none => .error (.missingExpression id)
      match node.form with
      | .integerLiteral literal resolution =>
          let validated ← (SourceCoreElaboration.validateWordIntegerLiteral context.solvedRequirements
            node literal resolution).mapError SourceCoreBasic.Error.literalEvidence
          pure ⟨.word, Core.LanguageResult.success (.word validated.value)⟩
      | _ =>
          let (node, type) ← (SourceCoreBasic.readExpression source id)
          let site := SourceCoreElaboration.ErrorSite.occurrence id.occurrence
          match node.form with
          | .call callee arguments (.declaration instantiation) =>
              let (globalIndex, signature) ← directSignature context source node callee arguments instantiation
              (SourceCoreBasic.ensureType site signature.resultType type)
              let arguments ← arguments.mapM fun argument =>
                lowerExpressionWithReasons fuel context source scope argument reasonAt
              let packed := packArguments arguments
              (SourceCoreBasic.ensureType site signature.parameterType packed.type)
              pure ⟨type, call signature (scope.length + context.administrativePrefix + globalIndex)
                packed.expression context.internalReason⟩
          | .unary operator operand =>
              let operand ← lowerExpressionWithReasons fuel context source scope operand reasonAt
              let coreOperator := SourceCorePrimitive.unaryOperator operator
              (SourceCoreBasic.ensureType site coreOperator.operandType operand.type)
              (SourceCoreBasic.ensureType site coreOperator.resultType type)
              pure ⟨type, Core.LocalPrimitiveResults.unary coreOperator operand.expression⟩
          | .binary left operator right =>
              let left ← lowerExpressionWithReasons fuel context source scope left reasonAt
              let right ← lowerExpressionWithReasons fuel context source scope right reasonAt
              (SourceCoreBasic.ensureType site (SourceCorePrimitive.binaryOperandType operator) left.type)
              (SourceCoreBasic.ensureType site (SourceCorePrimitive.binaryOperandType operator) right.type)
              (SourceCoreBasic.ensureType site (SourceCorePrimitive.binaryResultType operator) type)
              pure ⟨type, SourceCorePrimitive.binary operator left.expression right.expression⟩
          | .conditional condition thenBranch elseBranch =>
              let condition ← lowerExpressionWithReasons fuel context source scope condition reasonAt
              (SourceCoreBasic.ensureType site .bool condition.type)
              let thenBranch ← lowerExpressionWithReasons fuel context source scope thenBranch reasonAt
              let elseBranch ← lowerExpressionWithReasons fuel context source scope elseBranch reasonAt
              (SourceCoreBasic.ensureType site type thenBranch.type)
              (SourceCoreBasic.ensureType site type elseBranch.type)
              pure ⟨type, Core.LocalControl.choose type condition.expression thenBranch.expression elseBranch.expression⟩
          | .group inner =>
              let inner ← lowerExpressionWithReasons fuel context source scope inner reasonAt
              (SourceCoreBasic.ensureType site type inner.type)
              pure inner
          | .tuple [left, right] =>
              let left ← lowerExpressionWithReasons fuel context source scope left reasonAt
              let right ← lowerExpressionWithReasons fuel context source scope right reasonAt
              (SourceCoreBasic.ensureType site type (.product left.type right.type))
              pure ⟨type, Core.LocalSequence.pair left.type right.type left.expression right.expression⟩
          | _ => (SourceCoreBasic.lowerExpression (fuel + 1) source scope id (reasonAt id))

end Solcore.Frontend.SourceCoreCalls
