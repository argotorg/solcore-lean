import Solcore.Test.SourceCoreMixedImperativeFixture
import Solcore.Test.SourceCoreSelectedGeneralizedLocalTypingValidation
import Solcore.Test.SourceCoreGeneralizedExportTyping

/-! A bounded observer constructs declarative typing for the complete original
mixed body, including branches, lexical scopes, loops and bare variable writes. It accepts
only the expression and statement forms used by this regression. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedImperative
open Solcore Core Frontend SourceInference SourceSemantics
namespace OriginalValidation
open Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation

private def observe := @Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.observe
private def localFacts : StatementFacts :=
  ⟨.unit, false, false, .ordinary .unit⟩

private def parameters (owner : Resolved.DeclarationId) (context : SourceSemantics.Context) :
    (values : List TypedBinder) → IO ((final : SourceSemantics.Context) ×
      PLift (MonoBindersExtend owner context values (values.map (·.scheme.body)) final))
  | [] => pure ⟨context, ⟨.nil _⟩⟩
  | value :: rest => do
    let ⟨mono⟩ ← observe (value.scheme = .mono value.scheme.body) "mixed parameter scheme"
    let ⟨extended⟩ ← binder context owner value
    let ⟨final,⟨tail⟩⟩ ← parameters owner
      (context.withLocal value.id value.scheme value.schemeRequirements) rest
    return ⟨final, ⟨.cons mono extended tail⟩⟩

private def reference {source : TypedSource} (context : SourceSemantics.Context)
    (node : ExpressionNode) (found : source.lookupExpression? node.id = some node)
    (name : String) (id : Resolved.LocalId)
    (form : node.form = .reference name (.local id)) :
    IO (PLift (ExpressionHasType source context node.id node.type)) := do
  match schemeFound : Resolved.LocalScope.lookup? context.locals id with
  | none => throw (IO.userError "mixed local scheme lookup")
  | some schemeValue =>
    let ⟨requirements⟩ ← observe (Resolved.LocalScope.lookup? context.localSchemeRequirements id = some [])
      "mixed unqualified lexical reference"
    let value : TypedBinder := {id, name, scheme := schemeValue}
    let ⟨raw⟩ ← observe (node.rawType = node.type) "mixed local raw type"
    let ⟨empty⟩ ← observe (node.requirements = []) "mixed local requirements"
    let ⟨coercions⟩ ← observe (node.coercions = []) "mixed local coercions"
    let shape : Tests.SourceCoreNamedBranch.Read source value node.type := {
      node := node, found := found, form := form, raw := raw,
      type := rfl, requirements := empty, coercions := coercions }
    read shape context (Resolved.LocalScope.lookup?_iff.mp schemeFound)
      (Resolved.LocalScope.lookup?_iff.mp requirements)

private def writable (context : SourceSemantics.Context) (id : Resolved.LocalId) (type : TypeSystem.Ty) :
    IO (PLift (WritableLocal context id type)) := do
  match found : Resolved.LocalScope.lookup? context.locals id with
  | none => throw (IO.userError "mixed assignment root")
  | some actual =>
    let ⟨formed⟩ ← scheme context actual
    let ⟨mono⟩ ← observe (actual.quantified = []) "mixed writable monomorphic root"
    let ⟨same⟩ ← observe (actual.body = type) "mixed writable root type"
    return ⟨.intro (Resolved.LocalScope.lookup?_iff.mp found) formed mono same⟩

private def compound : (operator : Syntax.ValueAssignOp) → IO (PLift (WordCompoundAssignmentOperator operator))
  | .equal => throw (IO.userError "mixed compound operator")
  | .add => pure ⟨.add⟩
  | .subtract => pure ⟨.subtract⟩
  | .multiply => pure ⟨.multiply⟩
  | .divide => pure ⟨.divide⟩
  | .modulo => pure ⟨.modulo⟩
  | .bitAnd => pure ⟨.bitAnd⟩
  | .bitXor => pure ⟨.bitXor⟩
  | .bitOr => pure ⟨.bitOr⟩

structure Statement (source : TypedSource) (control : ControlContext)
    (context : SourceSemantics.Context) (id : StatementId) where
  final : SourceSemantics.Context
  facts : StatementFacts
  typed : StatementHasType source control context id final facts

structure Statements (source : TypedSource) (control : ControlContext)
    (context : SourceSemantics.Context) (ids : List StatementId) where
  final : SourceSemantics.Context
  facts : BodyFacts
  typed : StatementsHaveType source control context ids final facts

mutual
  def expression : (fuel : Nat) → (source : TypedSource) → (context : SourceSemantics.Context) →
      (id : ExpressionId) → (expected : TypeSystem.Ty) → IO (PLift (ExpressionHasType source context id expected))
    | 0, _, _, _, _ => throw (IO.userError "mixed typing expression bound")
    | fuel + 1, source, context, id, expected => do
      match found : source.lookupExpression? id with
      | none => throw (IO.userError "mixed original expression")
      | some node =>
        let ⟨same⟩ ← observe (node.id = id) "mixed original expression identity"
        let foundAt : source.lookupExpression? node.id = some node := same ▸ found
        let ⟨result⟩ ← observe (node.type = expected) "mixed expression result type"
        let ⟨typed⟩ ← (show IO (PLift (ExpressionHasType source context node.id node.type)) from do
          match form : node.form with
          | .reference name (.local localId) => reference context node foundAt name localId form
          | .reference _ (.builtinBoolean value) =>
            let ⟨typed⟩ ← uncoerced context node .bool foundAt (form ▸ .reference (.builtinBoolean value))
            let ⟨typeEq⟩ ← observe (node.type = .bool) "mixed Boolean type"
            return ⟨typeEq.symm ▸ typed⟩
          | .reference _ (.builtinFunction function) =>
            let ⟨typed⟩ ← uncoerced context node function.type foundAt (form ▸ .reference (.builtinFunction function))
            let ⟨typeEq⟩ ← observe (node.type = function.type) "mixed builtin function type"
            return ⟨typeEq.symm ▸ typed⟩
          | .integerLiteral literal resolution =>
            let ⟨target⟩ ← observe (resolution.targetType = .word) "mixed integer target"
            let ⟨requirements⟩ ← observe (node.requirements = [resolution.requirement]) "mixed integer requirements"
            let ⟨coercions⟩ ← observe (node.coercions = []) "mixed integer coercions"
            let ⟨typeEq⟩ ← observe (node.type = .word) "mixed integer type"
            let ⟨typed⟩ ← word ⟨node,literal,resolution,foundAt,form,target,requirements,coercions⟩ context
            return ⟨typeEq.symm ▸ typed⟩
          | .group inner =>
            let ⟨child⟩ ← expression fuel source context inner node.type
            uncoerced context node node.type foundAt (form ▸ .group child)
          | .tuple children =>
            let ⟨types,⟨childrenTyped⟩⟩ ← expressions fuel source context children
            let ⟨typeEq⟩ ← observe (node.type = TypeSystem.Ty.productMany types) "mixed tuple type"
            let ⟨typed⟩ ← uncoerced context node (TypeSystem.Ty.productMany types) foundAt (form ▸ .tuple childrenTyped)
            return ⟨typeEq.symm ▸ typed⟩
          | .call callee arguments (.indirect metadata) =>
            let ⟨types,⟨argumentsTyped⟩⟩ ← expressions fuel source context arguments
            let ⟨calleeTyped⟩ ← expression fuel source context callee
              (.function metadata.argumentTypeAfterCoercion node.type)
            let ⟨arity⟩ ← observe (metadata.argumentCount = types.length) "mixed call arity"
            let ⟨before⟩ ← observe (metadata.argumentTypeBeforeCoercion = TypeSystem.Ty.productMany types) "mixed call input"
            let ⟨after⟩ ← observe (metadata.argumentTypeAfterCoercion = TypeSystem.Ty.productMany types) "mixed call output"
            let ⟨argumentCoercions⟩ ← observe (metadata.argumentCoercions = []) "mixed call argument coercions"
            let ⟨raw⟩ ← observe (node.rawType = node.type) "mixed call raw type"
            let ⟨requirements⟩ ← observe (node.requirements = []) "mixed call requirements"
            let ⟨coercions⟩ ← observe (node.coercions = []) "mixed call coercions"
            let ⟨formed⟩ ← admissible context node.type
            have application : IndirectApplicationValid context metadata types metadata.argumentTypeAfterCoercion :=
              .intro arity before rfl (by rw [before,after,argumentCoercions]; exact .nil _)
            return ⟨.intro (lookupExpression?_sound foundAt)
              (form ▸ ExpressionFormHasRawType.indirectCall calleeTyped argumentsTyped application) raw formed formed (by
                rw [requirements,coercions,argumentCoercions]
                exact .indirectCall (by intro step member; cases member) (.nil _) rfl)⟩
          | .lambda values resultType body =>
            let ⟨unique⟩ ← observe ((values.map (·.name)).Nodup) "mixed lambda names"
            let ⟨lambdaContext,⟨extended⟩⟩ ← parameters source.owner context values
            let bodyTyped ← statements fuel source {returnType := resultType} lambdaContext body
            let ⟨completes⟩ ← observe (bodyTyped.facts.control.mayBreak = false ∧
              bodyTyped.facts.control.mayContinue = false ∧
              ((bodyTyped.facts.control.fallthrough = none ∧ bodyTyped.facts.control.mayReturn = true) ∨
                bodyTyped.facts.control.fallthrough = some resultType)) "mixed lambda completion"
            let type := TypeSystem.Ty.function (TypeSystem.Ty.productMany (values.map (·.scheme.body))) resultType
            let ⟨typeEq⟩ ← observe (node.type = type) "mixed lambda type"
            let ⟨typed⟩ ← uncoerced context node type foundAt
              (form ▸ .lambda unique extended bodyTyped.typed completes)
            return ⟨typeEq.symm ▸ typed⟩
          | _ => throw (IO.userError "unsupported original mixed expression"))
        return ⟨by simpa only [same,result] using typed⟩

  def expressions : (fuel : Nat) → (source : TypedSource) → (context : SourceSemantics.Context) →
      (ids : List ExpressionId) → IO ((types : List TypeSystem.Ty) × PLift (ExpressionsHaveTypes source context ids types))
    | 0, _, _, _ => throw (IO.userError "mixed typing expression sequence bound")
    | _ + 1, _, context, [] => pure ⟨[],⟨.nil context⟩⟩
    | fuel + 1, source, context, id :: rest => do
      let some node := source.lookupExpression? id | throw (IO.userError "mixed sequence original expression")
      let ⟨head⟩ ← expression fuel source context id node.type
      let ⟨types,⟨tail⟩⟩ ← expressions fuel source context rest
      return ⟨node.type :: types,⟨.cons head tail⟩⟩

  def statement : (fuel : Nat) → (source : TypedSource) → (control : ControlContext) →
      (context : SourceSemantics.Context) → (id : StatementId) → IO (Statement source control context id)
    | 0, _, _, _, _ => throw (IO.userError "mixed typing statement bound")
    | fuel + 1, source, control, context, id => do
      match found : source.lookupStatement? id with
      | none => throw (IO.userError "mixed original statement")
      | some node =>
        match form : node.form with
        | .letDecl value (some initializer) =>
          let ⟨extended⟩ ← binder context source.owner value
          let final := context.withLocal value.id value.scheme value.schemeRequirements
          let ⟨typeEq⟩ ← observe (node.type = .unit) "mixed declaration type"
          if mono : value.scheme.quantified = [] then
            let ⟨typed⟩ ← expression fuel source context initializer value.scheme.body
            match accepted : validateSchemeGeneralizes context value.scheme with
            | .error _ => throw (IO.userError "mixed ordinary generalization")
            | .ok () => return ⟨final,localFacts,.letInitialized (lookupStatement?_sound found) form typed mono
                (validateSchemeGeneralizes_success accepted) extended typeEq⟩
          else
            let ⟨requirements⟩ ← observe (value.schemeRequirements = []) "mixed generalized requirements"
            let ⟨generalized⟩ ← generalizes context value
            let ⟨typed⟩ ← expression fuel source (localSchemeInitializerContext context value) initializer value.scheme.body
            return ⟨final,localFacts,.letInitializedGeneralized (lookupStatement?_sound found) form mono
              (LocalSchemeRequirementsWellFormed.empty _ _ requirements) generalized typed extended typeEq⟩
        | .returnStmt (some value) =>
          let ⟨typed⟩ ← expression fuel source context value control.returnType
          let ⟨typeEq⟩ ← observe (node.type = control.returnType) "mixed return type"
          return ⟨context,⟨control.returnType,true,true,.returned⟩,
            .returnValue (lookupStatement?_sound found) form typed typeEq⟩
        | .expression value true =>
          let some child := source.lookupExpression? value | throw (IO.userError "mixed discarded expression")
          let ⟨typed⟩ ← expression fuel source context value child.type
          let ⟨typeEq⟩ ← observe (node.type = .unit) "mixed discard type"
          return ⟨context,localFacts,.expressionDiscard (lookupStatement?_sound found) form typed typeEq⟩
        | .forLoop initial condition post body =>
          let ⟨loopContext,⟨initialTyped⟩⟩ ← forItems fuel source control context initial
          let ⟨conditionTyped⟩ ← expression fuel source loopContext condition .bool
          let bodyTyped ← statements fuel source control.enterLoop loopContext body
          let ⟨_,⟨postTyped⟩⟩ ← forItems fuel source control.enterLoop loopContext post
          let ⟨typeEq⟩ ← observe (node.type = .unit) "mixed for type"
          return ⟨context,⟨.unit,false,false,.loop bodyTyped.facts.control⟩,
            .forLoop (lookupStatement?_sound found) form initialTyped conditionTyped bodyTyped.typed postTyped typeEq⟩
        | .whileLoop condition body =>
          let ⟨conditionTyped⟩ ← expression fuel source context condition .bool
          let bodyTyped ← statements fuel source control.enterLoop context body
          let ⟨typeEq⟩ ← observe (node.type = .unit) "mixed while type"
          return ⟨context,⟨.unit,false,false,.loop bodyTyped.facts.control⟩,
            .whileLoop (lookupStatement?_sound found) form conditionTyped bodyTyped.typed typeEq⟩
        | .assignValue assignment operator rhs =>
          let ⟨bare⟩ ← observe (assignment.target.projections = []) "mixed bare assignment"
          let ⟨rootTyped⟩ ← writable context assignment.target.root assignment.target.type
          let targetTyped : SourcePlaceHasType source context assignment.target assignment.target.type :=
            .intro rootTyped (bare.symm ▸ .nil _) rfl
          let ⟨rhsTyped⟩ ← expression fuel source context rhs assignment.target.type
          let ⟨requirements⟩ ← observe (assignment.requirements = []) "mixed assignment requirements"
          let ⟨typeEq⟩ ← observe (node.type = .unit) "mixed assignment statement type"
          let ⟨assignmentTyped⟩ ← (show IO (PLift (SourceAssignmentHasType source context assignment operator rhs)) from do
            if equal : operator = .equal then
              return ⟨equal.symm ▸ .equal targetTyped rhsTyped requirements⟩
            else
              let ⟨kind⟩ ← compound operator
              let ⟨word⟩ ← observe (assignment.target.type = .word) "mixed compound Word target"
              return ⟨.wordCompound kind (word ▸ targetTyped) (word ▸ rhsTyped) requirements⟩)
          return ⟨context,localFacts,.assignValue (lookupStatement?_sound found) form assignmentTyped typeEq⟩
        | .breakStmt =>
          let ⟨allowed⟩ ← observe (0 < control.loopDepth) "mixed break inside loop"
          let ⟨typeEq⟩ ← observe (node.type = .unit) "mixed break type"
          return ⟨context,⟨.unit,false,false,.breaking⟩,.breakStmt (lookupStatement?_sound found) form allowed typeEq⟩
        | .continueStmt =>
          let ⟨allowed⟩ ← observe (0 < control.loopDepth) "mixed continue inside loop"
          let ⟨typeEq⟩ ← observe (node.type = .unit) "mixed continue type"
          return ⟨context,⟨.unit,false,false,.continuing⟩,.continueStmt (lookupStatement?_sound found) form allowed typeEq⟩
        | .block body =>
          let child ← statements fuel source control context body
          let ⟨typeEq⟩ ← observe (node.type = child.facts.type) "mixed block type"
          return ⟨context,⟨child.facts.type,child.facts.sawReturn,child.facts.sawReturn,child.facts.control.eraseValue⟩,
            .block (lookupStatement?_sound found) form child.typed typeEq⟩
        | .ifThen condition yes (some no) =>
          let ⟨conditionTyped⟩ ← expression fuel source context condition .bool
          let yesTyped ← statements fuel source control context yes
          let noTyped ← statements fuel source control context no
          let returns := yesTyped.facts.sawReturn && noTyped.facts.sawReturn
          let type := if returns then control.returnType else .unit
          let ⟨typeEq⟩ ← observe (node.type = type) "mixed branch type"
          return ⟨context,⟨type,returns,returns,yesTyped.facts.control.branches noTyped.facts.control⟩,
            .ifWithElse (lookupStatement?_sound found) form conditionTyped yesTyped.typed noTyped.typed typeEq⟩
        | _ => throw (IO.userError "unsupported original mixed statement")

  def forItems : (fuel : Nat) → (source : TypedSource) → (control : ControlContext) →
      (context : SourceSemantics.Context) → (items : List ForItemForm) →
      IO ((final : SourceSemantics.Context) × PLift (ForItemsHaveType source control context items final))
    | 0, _, _, _, _ => throw (IO.userError "mixed typing for header bound")
    | _ + 1, _, control, context, [] => pure ⟨context,⟨.nil control context⟩⟩
    | fuel + 1, source, control, context, item :: rest => do
      let ⟨middle,⟨head⟩⟩ ← (show IO ((middle : SourceSemantics.Context) ×
          PLift (ForItemHasType source control context item middle)) from do
        match itemEq : item with
        | .letDecl value initializer =>
          let ⟨mono⟩ ← observe (value.scheme.quantified = []) "mixed for ordinary binder"
          let ⟨extended⟩ ← binder context source.owner value
          let final := context.withLocal value.id value.scheme value.schemeRequirements
          match accepted : validateSchemeGeneralizes context value.scheme with
          | .error _ => throw (IO.userError "mixed for ordinary generalization")
          | .ok () =>
            let generalized := validateSchemeGeneralizes_success accepted
            match initialEq : initializer with
            | none => return ⟨final,⟨by rw [itemEq,initialEq]; exact .letUninitialized mono generalized extended⟩⟩
            | some id =>
              let ⟨typed⟩ ← expression fuel source context id value.scheme.body
              return ⟨final,⟨by rw [itemEq,initialEq]; exact .letInitialized typed mono generalized extended⟩⟩
        | .expression id =>
          let some node := source.lookupExpression? id | throw (IO.userError "mixed for expression")
          let ⟨typed⟩ ← expression fuel source context id node.type
          return ⟨context,⟨itemEq.symm ▸ .expression typed⟩⟩
        | .assignValue assignment operator rhs =>
          let ⟨bare⟩ ← observe (assignment.target.projections = []) "mixed for bare assignment"
          let ⟨rootTyped⟩ ← writable context assignment.target.root assignment.target.type
          let targetTyped : SourcePlaceHasType source context assignment.target assignment.target.type :=
            .intro rootTyped (bare.symm ▸ .nil _) rfl
          let ⟨rhsTyped⟩ ← expression fuel source context rhs assignment.target.type
          let ⟨requirements⟩ ← observe (assignment.requirements = []) "mixed for assignment requirements"
          let ⟨assignmentTyped⟩ ← (show IO (PLift (SourceAssignmentHasType source context assignment operator rhs)) from do
            if equal : operator = .equal then
              return ⟨equal.symm ▸ .equal targetTyped rhsTyped requirements⟩
            else
              let ⟨kind⟩ ← compound operator
              let ⟨word⟩ ← observe (assignment.target.type = .word) "mixed for compound Word target"
              return ⟨.wordCompound kind (word ▸ targetTyped) (word ▸ rhsTyped) requirements⟩)
          return ⟨context,⟨itemEq.symm ▸ .assignValue assignmentTyped⟩⟩
        | .assignBitNot _ => throw (IO.userError "unsupported original mixed for unary assignment"))
      let ⟨final,⟨tail⟩⟩ ← forItems fuel source control middle rest
      return ⟨final,⟨.cons head tail⟩⟩

  def statements : (fuel : Nat) → (source : TypedSource) → (control : ControlContext) →
      (context : SourceSemantics.Context) → (ids : List StatementId) → IO (Statements source control context ids)
    | 0, _, _, _, _ => throw (IO.userError "mixed typing statement sequence bound")
    | _ + 1, _, control, context, [] => pure ⟨context,.empty,.nil control context⟩
    | fuel + 1, source, control, context, [id] => do
      let head ← statement fuel source control context id
      return ⟨head.final,.singleton head.facts,.singleton head.typed⟩
    | fuel + 1, source, control, context, id :: next :: rest => do
      let head ← statement fuel source control context id
      let tail ← statements fuel source control head.final (next :: rest)
      return ⟨tail.final,.cons head.facts tail.facts,.cons head.typed tail.typed⟩
end
end OriginalValidation

abbrev BodyTyping := Tests.SourceCoreGeneralizedExport.BodyTyping

def observeBodyTyping (signatures : ProgramSignatures) (function : CheckedFunction)
    (signature : ProgramFunctionSignature) : IO (BodyTyping signatures function signature) := do
  let base := checkedBodyContext signatures signature function
  let ⟨context,⟨inputs⟩⟩ ← OriginalValidation.parameters signature.id base function.typedBody.inputs
  let ⟨inputTypes⟩ ← observed (function.typedBody.inputs.map (·.scheme.body) = signature.parameterTypes) "mixed original input types"
  let roots ← function.typedBody.roots.mapM fun root => match root with
    | .statement id => pure id
    | .expression _ => throw (IO.userError "mixed original statement roots")
  let ⟨rootsEq⟩ ← observed (function.typedBody.roots = roots.map NodeId.statement) "mixed original complete roots"
  let result := TypeSystem.Ty.productMany signature.returnTypes
  let body ← OriginalValidation.statements 1000 function.typedBody {returnType := result} context roots
  let ⟨typeEq⟩ ← observed (body.facts.type = result) "mixed original whole body type"
  return ⟨roots,rootsEq,result,body.facts,typeEq,context,body.final,inputTypes ▸ inputs,body.typed,rfl⟩

end Tests.SourceCoreMixedImperative
