import Solcore.Frontend.SourceRuntime
import Solcore.Frontend.SourceSpecializationWorklist
import Solcore.Frontend.SourceCoreDirectLinking

/-!
Whole-program lowering to the finite runtime call-graph IR.

This linker is deliberately additive to the established Source-to-Core path.
The old linker remains authoritative for acyclic first-order programs and all
of its evidence-aware staging profiles.  This path retains runtime calls as
global references, so a finite definition table can represent direct and
mutual recursion without cyclic syntax.  The same IR also carries lexical
lambdas and indirect application.

The first profile is intentionally structural: runtime definitions must have
no signature assumptions or `comptime` contract, and evidence-bearing
operators/coercions remain with the old linker.  Checked Word literals retain
their exact builtin-`Int` obligation.  This restriction makes one canonical
specialization key determine one runtime definition body.
-/

set_option autoImplicit false

namespace Solcore.Frontend.SourceRuntimeLinking

open SourceInference TypeSystem

abbrev Key := SourceSpecialization.SpecializationKey
abbrev Plan := SourceSpecializationWorklist.Plan
abbrev RuntimeContext := List (Resolved.LocalId × Core.Ty)

inductive Error where
  | worklist (error : SourceSpecializationWorklist.Error)
  | invalidPlan (error : SourceCoreDirectLinking.Error)
  | budgetExhausted (next : Key) (pendingCount : Nat)
  | missingSpecialization (key : Key)
  | duplicateSpecializations (key : Key) (count : Nat)
  | unresolvedAssumptions (key : Key) (predicates : List ProgramPredicate)
  | comptimeContract
      (key : Key) (parameterComptime : List Bool) (returnComptime : Bool)
  | ownerMismatch
      (expected actual : Resolved.DeclarationId)
  | missingExpression (id : ExpressionId)
  | missingStatement (id : StatementId)
  | expectedStatementRoot (id : ExpressionId)
  | expressionDepthLimit (id : ExpressionId)
  | statementDepthLimit (id : StatementId)
  | unsupportedType (type : Ty)
  | duplicateLocal (id : Resolved.LocalId)
  | unknownLocal (id : Resolved.LocalId)
  | polymorphicLocal (id : Resolved.LocalId) (variables : List TypeVarId)
  | markedLocal (id : Resolved.LocalId)
  | localTypeMismatch (id : Resolved.LocalId) (expected actual : Core.Ty)
  | typedNodeTypeMismatch
      (occurrence : OccurrenceId) (expected actual : Core.Ty)
  | invalidWordLiteral (occurrence : OccurrenceId)
  | integerLiteralMetadata (occurrence : OccurrenceId)
  | missingRequirement (id : RequirementId)
  | duplicateRequirements (id : RequirementId) (count : Nat)
  | integerLiteralPredicateMismatch
      (id : RequirementId) (expected actual : ProgramPredicate)
  | requirementsUnsupported
      (occurrence : OccurrenceId) (requirements : List RequirementId)
  | requirementsMismatch
      (key : Key) (expected actual : List RequirementId)
  | coercionsUnsupported
      (occurrence : OccurrenceId) (coercions : List CoercionStep)
  | declarationReferenceMissingEdge (caller : Key) (occurrence : ExpressionId)
  | declarationReferenceDuplicateEdges
      (caller : Key) (occurrence : ExpressionId) (count : Nat)
  | declarationReferenceCalleeMismatch
      (caller : Key) (occurrence : ExpressionId) (expected actual : Key)
  | directCallMissingEdge (caller : Key) (occurrence : ExpressionId)
  | directCallDuplicateEdges
      (caller : Key) (occurrence : ExpressionId) (count : Nat)
  | directCallCalleeMismatch
      (caller : Key) (occurrence : ExpressionId) (expected actual : Key)
  | callCalleeMismatch (call callee : ExpressionId)
  | callArityMismatch (occurrence : ExpressionId) (expected actual : Nat)
  | callTypeMismatch (occurrence : ExpressionId) (expected actual : Ty)
  | indirectCalleeNotFunction (occurrence : ExpressionId) (type : Ty)
  | indirectArgumentTypeMismatch
      (occurrence : ExpressionId) (expected actual : Ty)
  | indirectArgumentCoercionsUnsupported
      (occurrence : ExpressionId) (coercions : List CoercionStep)
  | lambdaTypeMismatch (occurrence : ExpressionId) (expected actual : Ty)
  | unsupportedExpression (occurrence : ExpressionId)
  | unsupportedStatement (occurrence : StatementId)
  | uninitializedLet (occurrence : StatementId)
  | nonTailStatement (occurrence : StatementId)
  | missingElseBranch (occurrence : StatementId)
  | statementFallthrough (owner : Resolved.DeclarationId)
  | runtimeType (error : SourceRuntime.TypeError)
  | linkedResultTypeMismatch (key : Key) (source runtime : Core.Ty)
  | publicResultUnsupported (type : Core.Ty)
  | compatibilitySourceCore (error : SourceCoreElaboration.Error)
  deriving Repr

/-- The structural source-to-Core projection admitted by the finite call-graph
linker.  Unlike direct Core lowering, this projection also admits function
types for runtime globals and closures. -/
def lowerType : Ty → Except Error Core.Ty
  | .constructor (.builtin .unit) => pure .unit
  | .constructor (.builtin .bool) => pure .bool
  | .constructor (.builtin .word) => pure .word
  | .product left right => do
      pure (.product (← lowerType left) (← lowerType right))
  | .function parameter result => do
      pure (.function (← lowerType parameter) (← lowerType result))
  | type => throw (.unsupportedType type)

structure LinkedEntry where
  key : Key
  inputs : RuntimeContext
  resultType : Core.Ty
  /-- The inferred result type of the specialization selected by `key`. -/
  sourceBodyType : Ty
  /-- A public certificate that the entry result uses that source type. -/
  resultType_eq_source : lowerType sourceBodyType = .ok resultType
  program : SourceRuntime.CheckedProgram
  /-- The executable table exposes this same result type at the entry key. -/
  signatureResultType : ∃ signature,
    program.entrySignature? key = some signature ∧
    signature.resultType = resultType
  deriving Repr

structure LinkedProgram where
  entries : List LinkedEntry
  deriving Repr

private structure Lowered where
  expr : SourceRuntime.Expr
  consumed : List RequirementId

private structure Context where
  program : CheckedProgram
  plan : Plan
  specialized : SourceSpecialization.SpecializedFunction
  source : TypedSource

private def lowerBinder (source : TypedSource) (binder : TypedBinder) :
    Except Error SourceRuntime.Parameter := do
  if binder.id.owner != source.owner then
    throw (.ownerMismatch source.owner binder.id.owner)
  unless binder.scheme.quantified.isEmpty do
    throw (.polymorphicLocal binder.id binder.scheme.quantified)
  if binder.comptime then
    throw (.markedLocal binder.id)
  pure (binder.id, ← lowerType binder.scheme.body)

private def lookupExpression (source : TypedSource) (id : ExpressionId) :
    Except Error ExpressionNode :=
  match source.lookupExpression? id with
  | some node => pure node
  | none => throw (.missingExpression id)

private def lookupStatement (source : TypedSource) (id : StatementId) :
    Except Error StatementNode :=
  match source.lookupStatement? id with
  | some node => pure node
  | none => throw (.missingStatement id)

private def scopeType? (scope : RuntimeContext)
    (id : Resolved.LocalId) : Option Core.Ty :=
  (scope.find? fun entry => decide (entry.1 = id)).map Prod.snd

private def ensureNodeType (node : ExpressionNode) (expected : Core.Ty) :
    Except Error Unit := do
  let actual ← lowerType node.type
  unless actual = expected do
    throw (.typedNodeTypeMismatch node.id.occurrence expected actual)

private def exactRequirement (requirements : List SolvedRequirement)
    (id : RequirementId) : Except Error SolvedRequirement :=
  match requirements.filter fun requirement => decide (requirement.id = id) with
  | [] => throw (.missingRequirement id)
  | [requirement] => pure requirement
  | found => throw (.duplicateRequirements id found.length)

private def exactSpecialization (plan : Plan) (key : Key) :
    Except Error SourceSpecialization.SpecializedFunction :=
  match plan.specializations.filter fun specialized =>
      decide (specialized.key = key) with
  | [] => throw (.missingSpecialization key)
  | [specialized] => pure specialized
  | found => throw (.duplicateSpecializations key found.length)

private def exactCallEdge (plan : Plan) (caller : Key)
    (occurrence : ExpressionId) :
    Except Error SourceSpecializationWorklist.CallEdge :=
  match plan.callEdges.filter fun edge =>
      decide (edge.caller = caller && edge.occurrence = occurrence) with
  | [] => throw (.directCallMissingEdge caller occurrence)
  | [edge] => pure edge
  | found => throw (.directCallDuplicateEdges caller occurrence found.length)

private def exactReferenceEdge (plan : Plan) (caller : Key)
    (occurrence : ExpressionId) :
    Except Error SourceSpecializationWorklist.ReferenceEdge :=
  match plan.referenceEdges.filter fun edge =>
      decide (edge.caller = caller && edge.occurrence = occurrence) with
  | [] => throw (.declarationReferenceMissingEdge caller occurrence)
  | [edge] => pure edge
  | found =>
      throw (.declarationReferenceDuplicateEdges caller occurrence found.length)

private def productExpression : List SourceRuntime.Expr → SourceRuntime.Expr
  | [] => .unit
  | [expression] => expression
  | expression :: rest => .pair expression (productExpression rest)

private def directBinary (operator : Syntax.BinaryOp)
    (left right : SourceRuntime.Expr) : SourceRuntime.Expr :=
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

private def statementRoots : List NodeId → Except Error (List StatementId)
  | [] => pure []
  | .statement id :: rest => do pure (id :: (← statementRoots rest))
  | .expression id :: _ => throw (.expectedStatementRoot id)

private def resolvedReferenceKey (context : Context)
    (instantiation : DeclarationInstantiation) : Except Error Key := do
  let specialized ←
    (SourceSpecializationWorklist.resolveRequest context.program {
      declaration := instantiation.declaration
      parameterSubstitution := instantiation.parameterSubstitution
    }).mapError Error.worklist
  pure specialized.key

private def ensureNoCoercions (node : ExpressionNode) : Except Error Unit :=
  unless node.coercions.isEmpty do
    throw (.coercionsUnsupported node.id.occurrence node.coercions)

mutual

private def lowerExpressionFuel (context : Context)
    (scope : RuntimeContext) : Nat → ExpressionId → Except Error Lowered
  | 0, id => throw (.expressionDepthLimit id)
  | fuel + 1, id => do
      let node ← lookupExpression context.source id
      ensureNoCoercions node
      match node.form with
      | .literal literal =>
          if node.requirements.isEmpty then
            match interpretWordLiteral? ⟨node.span, literal⟩ with
            | some word => pure { expr := .word word, consumed := [] }
            | none => throw (.invalidWordLiteral node.id.occurrence)
          else
            throw (.requirementsUnsupported node.id.occurrence
              node.requirements)
      | .integerLiteral source resolution => do
          if node.type != .word || resolution.targetType != .word ||
              node.requirements != [resolution.requirement] then
            throw (.integerLiteralMetadata node.id.occurrence)
          let rawValue ← match numericLiteralValue? source with
            | some value => pure value
            | none => throw (.invalidWordLiteral node.id.occurrence)
          if rawValue != resolution.rawValue then
            throw (.integerLiteralMetadata node.id.occurrence)
          let decoded := Core.Word.ofNatModulo rawValue
          let solved ← exactRequirement
            context.specialized.function.solvedRequirements
            resolution.requirement
          let expected := ProgramSignatures.builtinIntPredicate .word
          if solved.predicate != expected then
            throw (.integerLiteralPredicateMismatch resolution.requirement
              expected solved.predicate)
          pure { expr := .word decoded, consumed := node.requirements }
      | .reference _ (.local binder) => do
          unless node.requirements.isEmpty do
            throw (.requirementsUnsupported node.id.occurrence
              node.requirements)
          let expected ← lowerType node.type
          match scopeType? scope binder with
          | none => throw (.unknownLocal binder)
          | some actual =>
              unless actual = expected do
                throw (.localTypeMismatch binder expected actual)
          pure { expr := .local binder, consumed := [] }
      | .reference _ (.builtinBoolean value) => do
          unless node.requirements.isEmpty do
            throw (.requirementsUnsupported node.id.occurrence
              node.requirements)
          ensureNodeType node .bool
          pure { expr := .bool value, consumed := [] }
      | .reference _ (.declaration instantiation) => do
          unless node.requirements.isEmpty do
            throw (.requirementsUnsupported node.id.occurrence
              node.requirements)
          let expected ← resolvedReferenceKey context instantiation
          let edge ← exactReferenceEdge context.plan context.specialized.key id
          unless edge.callee = expected do
            throw (.declarationReferenceCalleeMismatch
              context.specialized.key id expected edge.callee)
          let target ← exactSpecialization context.plan edge.callee
          let markers := target.function.typedBody.inputs.map (·.comptime)
          if markers.any (fun marked => marked) ||
              target.function.returnComptime then
            throw (.comptimeContract target.key markers
              target.function.returnComptime)
          pure { expr := .global edge.callee, consumed := [] }
      | .reference _ (.builtinFunction _) =>
          throw (.unsupportedExpression id)
      | .group inner => lowerExpressionFuel context scope fuel inner
      | .tuple elements => do
          unless node.requirements.isEmpty do
            throw (.requirementsUnsupported node.id.occurrence
              node.requirements)
          let lowered ← elements.mapM (lowerExpressionFuel context scope fuel)
          pure {
            expr := productExpression (lowered.map (·.expr))
            consumed := lowered.flatMap (·.consumed)
          }
      | .unary operator operand => do
          unless node.requirements.isEmpty do
            throw (.requirementsUnsupported node.id.occurrence
              node.requirements)
          let lowered ← lowerExpressionFuel context scope fuel operand
          pure {
            expr := .unary (match operator with
              | .logicalNot => .boolNot
              | .bitNot => .wordNot) lowered.expr
            consumed := lowered.consumed
          }
      | .binary left operator right => do
          unless node.requirements.isEmpty do
            throw (.requirementsUnsupported node.id.occurrence
              node.requirements)
          let loweredLeft ← lowerExpressionFuel context scope fuel left
          let loweredRight ← lowerExpressionFuel context scope fuel right
          pure {
            expr := directBinary operator loweredLeft.expr loweredRight.expr
            consumed := loweredLeft.consumed ++ loweredRight.consumed
          }
      | .conditional condition thenBranch elseBranch => do
          unless node.requirements.isEmpty do
            throw (.requirementsUnsupported node.id.occurrence
              node.requirements)
          let loweredCondition ←
            lowerExpressionFuel context scope fuel condition
          let loweredThen ← lowerExpressionFuel context scope fuel thenBranch
          let loweredElse ← lowerExpressionFuel context scope fuel elseBranch
          pure {
            expr := .ifE loweredCondition.expr loweredThen.expr
              loweredElse.expr
            consumed := loweredCondition.consumed ++ loweredThen.consumed ++
              loweredElse.consumed
          }
      | .lambda parameters resultType body => do
          unless node.requirements.isEmpty do
            throw (.requirementsUnsupported node.id.occurrence
              node.requirements)
          let loweredParameters ← parameters.mapM (lowerBinder context.source)
          let ids := loweredParameters.map Prod.fst
          let scopeIds := scope.map Prod.fst
          if ids.eraseDups.length != ids.length ||
              ids.any (fun parameter => scopeIds.contains parameter) then
            let duplicate := ids.find? fun parameter =>
              scopeIds.contains parameter || ids.count parameter > 1
            match duplicate with
            | some parameter => throw (.duplicateLocal parameter)
            | none => throw (.unsupportedExpression id)
          let loweredResult ← lowerType resultType
          let expectedType := Ty.function
            (Ty.productMany (parameters.map (·.scheme.body))) resultType
          if node.rawType != expectedType then
            throw (.lambdaTypeMismatch id node.rawType expectedType)
          let loweredBody ← lowerStatementsFuel context
            (loweredParameters ++ scope) loweredResult fuel body
          pure {
            expr := .lambda loweredParameters loweredResult loweredBody.expr
            consumed := loweredBody.consumed
          }
      | .call callee arguments (.declaration instantiation) => do
          unless node.requirements.isEmpty do
            throw (.requirementsUnsupported node.id.occurrence
              node.requirements)
          let expected ← resolvedReferenceKey context instantiation
          let edge ← exactCallEdge context.plan context.specialized.key id
          unless edge.callee = expected do
            throw (.directCallCalleeMismatch context.specialized.key id
              expected edge.callee)
          let calleeNode ← lookupExpression context.source callee
          match calleeNode.form with
          | .reference _ (.declaration reference) =>
              unless reference = instantiation do
                throw (.callCalleeMismatch id callee)
          | _ => throw (.callCalleeMismatch id callee)
          let target ← exactSpecialization context.plan edge.callee
          let markers := target.function.typedBody.inputs.map (·.comptime)
          if markers.any (fun marked => marked) ||
              target.function.returnComptime then
            throw (.comptimeContract target.key markers
              target.function.returnComptime)
          if arguments.length != target.function.typedBody.inputs.length then
            throw (.callArityMismatch id
              target.function.typedBody.inputs.length arguments.length)
          let lowered ← arguments.mapM
            (lowerExpressionFuel context scope fuel)
          pure {
            expr := .apply (.global edge.callee) (lowered.map (·.expr))
            consumed := lowered.flatMap (·.consumed)
          }
      | .call callee arguments (.indirect metadata) => do
          unless node.requirements.isEmpty do
            throw (.requirementsUnsupported node.id.occurrence
              node.requirements)
          unless metadata.argumentCoercions.isEmpty do
            throw (.indirectArgumentCoercionsUnsupported id
              metadata.argumentCoercions)
          let calleeNode ← lookupExpression context.source callee
          let (parameterType, resultType) ← match calleeNode.type with
            | .function parameter result => pure (parameter, result)
            | other => throw (.indirectCalleeNotFunction id other)
          let argumentNodes ← arguments.mapM (lookupExpression context.source)
          let bundled := Ty.productMany (argumentNodes.map (·.type))
          if metadata.argumentTypeBeforeCoercion != bundled then
            throw (.indirectArgumentTypeMismatch id bundled
              metadata.argumentTypeBeforeCoercion)
          if metadata.argumentTypeAfterCoercion != parameterType then
            throw (.indirectArgumentTypeMismatch id parameterType
              metadata.argumentTypeAfterCoercion)
          if node.rawType != resultType then
            throw (.callTypeMismatch id resultType node.rawType)
          let loweredCallee ← lowerExpressionFuel context scope fuel callee
          let loweredArguments ← arguments.mapM
            (lowerExpressionFuel context scope fuel)
          pure {
            expr := .apply loweredCallee.expr
              (loweredArguments.map (·.expr))
            consumed := loweredCallee.consumed ++
              loweredArguments.flatMap (·.consumed)
          }
      | .call _ _ (.builtinFunction _) =>
          throw (.unsupportedExpression id)
      | .constructor _ _
      | .member _ _ _
      | .proxy _
      | .index _ _ => throw (.unsupportedExpression id)

private def lowerStatementsFuel (context : Context)
    (scope : RuntimeContext) (expected : Core.Ty) :
    Nat → List StatementId → Except Error Lowered
  | _, [] => throw (.statementFallthrough context.source.owner)
  | 0, id :: _ => throw (.statementDepthLimit id)
  | fuel + 1, id :: rest => do
      let node ← lookupStatement context.source id
      match node.form with
      | .letDecl binder initializer => do
          if (scope.map Prod.fst).contains binder.id then
            throw (.duplicateLocal binder.id)
          unless binder.scheme.quantified.isEmpty do
            throw (.polymorphicLocal binder.id binder.scheme.quantified)
          if binder.comptime then
            throw (.markedLocal binder.id)
          let binderType ← lowerType binder.scheme.body
          let initializer ← match initializer with
            | some initializer => pure initializer
            | none => throw (.uninitializedLet id)
          let loweredInitializer ←
            lowerExpressionFuel context scope fuel initializer
          let initializerNode ← lookupExpression context.source initializer
          ensureNodeType initializerNode binderType
          let loweredBody ← lowerStatementsFuel context
            ((binder.id, binderType) :: scope) expected fuel rest
          pure {
            expr := .letE binder.id loweredInitializer.expr loweredBody.expr
            consumed := loweredInitializer.consumed ++ loweredBody.consumed
          }
      | .returnStmt value => do
          unless rest.isEmpty do throw (.nonTailStatement id)
          match value with
          | none =>
              if expected = .unit then
                pure { expr := .unit, consumed := [] }
              else
                throw (.typedNodeTypeMismatch id.occurrence expected .unit)
          | some value => do
              let valueNode ← lookupExpression context.source value
              ensureNodeType valueNode expected
              lowerExpressionFuel context scope fuel value
      | .ifThen condition thenBody elseBody => do
          unless rest.isEmpty do throw (.nonTailStatement id)
          let elseBody ← match elseBody with
            | some body => pure body
            | none => throw (.missingElseBranch id)
          let conditionNode ← lookupExpression context.source condition
          ensureNodeType conditionNode .bool
          let loweredCondition ←
            lowerExpressionFuel context scope fuel condition
          let loweredThen ← lowerStatementsFuel context scope expected fuel
            thenBody
          let loweredElse ← lowerStatementsFuel context scope expected fuel
            elseBody
          pure {
            expr := .ifE loweredCondition.expr loweredThen.expr
              loweredElse.expr
            consumed := loweredCondition.consumed ++ loweredThen.consumed ++
              loweredElse.consumed
          }
      | .block body => do
          unless rest.isEmpty do throw (.nonTailStatement id)
          lowerStatementsFuel context scope expected fuel body
      | .matchWith _
      | .expression _ _
      | .assignValue _ _ _
      | .assignBitNot _
      | .forLoop _ _ _ _
      | .whileLoop _ _
      | .breakStmt
      | .continueStmt =>
          throw (.unsupportedStatement id)

end

private def lowerDefinition (program : CheckedProgram) (plan : Plan)
    (specialized : SourceSpecialization.SpecializedFunction) :
    Except Error { definition : SourceRuntime.Definition //
      lowerType specialized.function.inferredBodyType = .ok definition.resultType } := do
  unless specialized.assumptions.isEmpty do
    throw (.unresolvedAssumptions specialized.key specialized.assumptions)
  let function := specialized.function
  let source := function.typedBody
  if source.owner != specialized.declaration then
    throw (.ownerMismatch specialized.declaration source.owner)
  let parameterComptime := source.inputs.map (·.comptime)
  if parameterComptime.any (fun marked => marked) || function.returnComptime then
    throw (.comptimeContract specialized.key parameterComptime
      function.returnComptime)
  let parameters ← source.inputs.mapM (lowerBinder source)
  match projection : lowerType function.inferredBodyType with
  | .error error => throw error
  | .ok resultType =>
      let roots ← statementRoots source.roots
      let context : Context := { program, plan, specialized, source }
      let lowered ← lowerStatementsFuel context parameters resultType
        (source.nodes.length + 1) roots
      let expectedRequirements := function.solvedRequirements.map (·.id)
      if lowered.consumed != expectedRequirements then
        throw (.requirementsMismatch specialized.key expectedRequirements
          lowered.consumed)
      let definition : SourceRuntime.Definition := {
        key := specialized.key
        parameters
        resultType
        body := lowered.expr
      }
      pure ⟨definition, by
        simpa only [definition] using projection⟩

private def linkedEntry (checked : SourceRuntime.CheckedProgram)
    (plan : Plan) (key : Key) : Except Error LinkedEntry := do
  let specialized ← exactSpecialization plan key
  match found : checked.program.findDefinition? key with
  | none => throw (.missingSpecialization key)
  | some definition =>
      match projected : lowerType specialized.function.inferredBodyType with
      | .error error => throw error
      | .ok sourceResultType =>
          if sameType : definition.resultType = sourceResultType then
            pure {
              key
              inputs := definition.parameters
              resultType := definition.resultType
              sourceBodyType := specialized.function.inferredBodyType
              resultType_eq_source := by simpa only [sameType] using projected
              program := checked
              signatureResultType := by
                refine ⟨definition.signature, ?_, rfl⟩
                simp [SourceRuntime.CheckedProgram.entrySignature?,
                  SourceRuntime.Program.findSignature?, found]
            }
          else
            throw (.linkedResultTypeMismatch key sourceResultType definition.resultType)

/-- Lower every canonical specialization once, check the complete table under
all signatures simultaneously, and recover entries in seed order. -/
def link (program : CheckedProgram)
    (outcome : SourceSpecializationWorklist.Outcome) :
    Except Error LinkedProgram := do
  let plan ← match outcome with
    | .complete plan => pure plan
    | .budgetExhausted _ next pending =>
        throw (.budgetExhausted next pending.length)
  SourceCoreDirectLinking.validatePlan program plan
    |>.mapError Error.invalidPlan
  let definitions ← plan.specializations.mapM fun specialized => do
    let certified ← lowerDefinition program plan specialized
    pure certified.val
  let checked ← ({ definitions } : SourceRuntime.Program).check
    |>.mapError Error.runtimeType
  pure {
    entries := ← plan.seedKeys.mapM (linkedEntry checked plan)
  }

private def defaultResolved : Core.Ty → Option Resolved.Expr
  | .unit => some .unit
  | .bool => some (.bool false)
  | .word => some (.word Core.Word.zero)
  | .product left right => do
      pure (.pair (← defaultResolved left) (← defaultResolved right))
  | .function _ _
  | .sum _ _
  | .cell _
  | .namedData _ => none

/-- Preserve the established linked-entry API while attaching the checked
runtime table which is authoritative for execution.  The closed resolved term
is only a type-correct first-order inspection view; `LinkedEntry.run?`
dispatches through `runtime`. -/
def LinkedEntry.toCoreLinkedEntry (entry : LinkedEntry) :
    Except Error SourceCoreDirectLinking.LinkedEntry := do
  let resolved ← match defaultResolved entry.resultType with
    | some resolved => pure resolved
    | none => throw (.publicResultUnsupported entry.resultType)
  let draft : SourceCoreElaboration.BodyDraft := {
    declaration := entry.key.declaration
    inputs := entry.inputs
    resolved
    returnType := entry.resultType
    rootOccurrence := ⟨entry.key.declaration, 0⟩
    unconsumedRequirements := []
  }
  let elaborated ← draft.finalize.mapError Error.compatibilitySourceCore
  pure {
    key := entry.key
    elaborated
    runtime := some entry.program
  }

def LinkedProgram.toCoreLinkedProgram (program : LinkedProgram) :
    Except Error SourceCoreDirectLinking.LinkedProgram := do
  pure { entries := ← program.entries.mapM LinkedEntry.toCoreLinkedEntry }

end Solcore.Frontend.SourceRuntimeLinking
