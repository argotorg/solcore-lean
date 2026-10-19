import Solcore.SourceSemantics.CoreLowering.CellAwareForHeaderAdmission
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeTypedSourceSites
import Solcore.SourceSemantics.CoreLowering.ScopedSourceForItemsAdmission
import Solcore.SourceSemantics.CoreLowering.CellAwareFaultingSourceBodyAdmission

/-! The common mixed body profile follows original lexical statement nodes.
The finite scanner retains compiler-visible syntax; original declarative typing
supplies every source context and child expression typing. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareImperativeSourceBodyAdmission
open Core Frontend SourceInference TypeSystem SourceCoreLocalPolymorphism
open CellAwareSourceBodyAdmission (Site site?)

inductive Scan (locals : Catalog) (caller : Key) (active : Substitution)
    (source : TypedSource) (approved : ExpressionId → Prop) (expected : TypeSystem.Ty) :
    Bool → List StatementId → Prop where
  | nil {mode} (allowed : mode = false ∨ expected = .unit) :
      Scan locals caller active source approved expected mode []
  | returnUnit {mode id node} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt none)
      (sourceType : node.type = .unit) (unit : expected = .unit) :
      Scan locals caller active source approved expected mode (id :: rest)
  | returning {mode id node expression expressionNode} (rest : List StatementId)
      (found : source.lookupStatement? id = some node)
      (form : node.form = .returnStmt (some expression))
      (sourceType : node.type = expected)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected) (value : approved expression) :
      Scan locals caller active source approved expected mode (id :: rest)
  | tail {id node expression expressionNode}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression false)
      (sourceType : node.type = expected)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected) (value : approved expression) :
      Scan locals caller active source approved expected true [id]
  | generalizedInitialized {mode id node binder initializer initializerNode parameters result body rest}
      (found : source.lookupStatement? id = some node)
      (form : node.form = .letDecl binder (some initializer))
      (sourceType : node.type = .unit)
      (declaration : (SourceCoreDataPlaces.declaredBinders source).filter (fun actual => decide (actual.id = binder.id)) = [binder])
      (polymorphic : binder.scheme.quantified ≠ [])
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (initializerForm : initializerNode.form = .lambda parameters result body)
      (valueType : initializerNode.type = binder.scheme.body)
      (requirements : initializerNode.requirements = []) (coercions : initializerNode.coercions = [])
      (site : Site locals caller active source binder initializer)
      (remaining : Scan locals caller active source approved expected mode rest) :
      Scan locals caller active source approved expected mode (id :: rest)
  | initialized {mode id node binder initializer initializerNode rest}
      (found : source.lookupStatement? id = some node)
      (form : node.form = .letDecl binder (some initializer))
      (sourceType : node.type = .unit)
      (declaration : (SourceCoreDataPlaces.declaredBinders source).filter
        (fun actual => decide (actual.id = binder.id)) = [binder])
      (mono : binder.scheme.quantified = [])
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (valueType : initializerNode.type = binder.scheme.body)
      (value : approved initializer)
      (remaining : Scan locals caller active source approved expected mode rest) :
      Scan locals caller active source approved expected mode (id :: rest)

  | uninitialized {mode id node binder rest}
      (found : source.lookupStatement? id = some node)
      (form : node.form = .letDecl binder none)
      (sourceType : node.type = .unit)
      (declaration : (SourceCoreDataPlaces.declaredBinders source).filter
        (fun actual => decide (actual.id = binder.id)) = [binder])
      (mono : binder.scheme.quantified = [])
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (remaining : Scan locals caller active source approved expected mode rest) :
      Scan locals caller active source approved expected mode (id :: rest)
  | discard {mode id node expression expressionNode semicolon rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression semicolon)
      (notTail : (!semicolon && mode && rest.isEmpty) = false)
      (continuing : semicolon = true ∨ mode = false)
      (expressionFound : source.lookupExpression? expression = some expressionNode) (value : approved expression)
      (remaining : Scan locals caller active source approved expected mode rest) :
      Scan locals caller active source approved expected mode (id :: rest)
  | block {mode id node statements rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
      (inner : Scan locals caller active source approved expected false statements)
      (remaining : Scan locals caller active source approved expected mode rest) :
      Scan locals caller active source approved expected mode (id :: rest)
  | ifThen {mode id node condition conditionNode thenBody elseBody rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
      (conditionFound : source.lookupExpression? condition = some conditionNode) (conditionType : conditionNode.type = .bool)
      (conditionSyntax : approved condition)
      (thenTree : Scan locals caller active source approved expected false thenBody)
      (elseTree : Scan locals caller active source approved expected false (elseBody.getD []))
      (remaining : Scan locals caller active source approved expected mode rest) :
      Scan locals caller active source approved expected mode (id :: rest)

  | whileLoop {mode id node condition conditionNode statements rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
      (conditionFound : source.lookupExpression? condition = some conditionNode) (conditionType : conditionNode.type = .bool)
      (conditionSyntax : approved condition)
      (loopTree : Scan locals caller active source approved expected false statements)
      (remaining : Scan locals caller active source approved expected mode rest) :
      Scan locals caller active source approved expected mode (id :: rest)
  | forLoop {mode id node initialItems condition conditionNode postItems statements rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .forLoop initialItems condition postItems statements)
      (initialTree : CellAwareForHeaderAdmission.Scan source approved initialItems)
      (conditionFound : source.lookupExpression? condition = some conditionNode) (conditionType : conditionNode.type = .bool)
      (conditionSyntax : approved condition)
      (loopTree : Scan locals caller active source approved expected false statements)
      (postTree : CellAwareForHeaderAdmission.Scan source approved postItems)
      (remaining : Scan locals caller active source approved expected mode rest) :
      Scan locals caller active source approved expected mode (id :: rest)
  | assign {mode id node assignment operator rhs rhsNode binder rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment operator rhs)
      (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
      (targetType : binder.scheme.body = assignment.target.type)
      (profile : operator = .equal ∨ assignment.target.type = .word)
      (bare : assignment.target.projections = [])
      (rhsFound : source.lookupExpression? rhs = some rhsNode)
      (rhsType : rhsNode.type = assignment.target.type) (value : approved rhs)
      (remaining : Scan locals caller active source approved expected mode rest) :
      Scan locals caller active source approved expected mode (id :: rest)

  | breaking {mode id node} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .breakStmt) :
      Scan locals caller active source approved expected mode (id :: rest)
  | continuing {mode id node} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .continueStmt) :
      Scan locals caller active source approved expected mode (id :: rest)

  | assignProjected {mode id node assignment operator rhs rhsNode binder rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment operator rhs)
      (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
      (route : AcceptedProjectedAssignmentRoute.Route source binder.scheme.body assignment.target.projections assignment.target.type)
      (profile : operator = .equal ∨ assignment.target.type = .word)
      (projected : assignment.target.projections ≠ [])
      (keys : ∀ key ∈ DataPlaceKeyOrder.sourceKeys assignment.target.projections, approved key)
      (rhsFound : source.lookupExpression? rhs = some rhsNode)
      (rhsType : rhsNode.type = assignment.target.type)
      (value : approved rhs)
      (remaining : Scan locals caller active source approved expected mode rest) :
      Scan locals caller active source approved expected mode (id :: rest)


def scan? (locals : Catalog) (caller : Key) (active : Substitution)
    (source : TypedSource) {approved : ExpressionId → Prop}
    (expression : (id : ExpressionId) → Option (PLift (approved id))) (expected : TypeSystem.Ty) :
    (fuel : Nat) → (mode : Bool) → (statements : List StatementId) →
      Option (PLift (Scan locals caller active source approved expected mode statements))
  | 0, _, _ => none
  | _ + 1, mode, [] => if allowed : mode = false ∨ expected = .unit then some ⟨.nil allowed⟩ else none
  | fuel + 1, mode, id :: rest =>
    match found : source.lookupStatement? id with
    | none => none
    | some node =>
      match form : node.form with
      | .returnStmt none =>
        if sourceType : node.type = .unit then
          if unit : expected = .unit then some ⟨.returnUnit rest found form sourceType unit⟩ else none
        else none
      | .returnStmt (some value) =>
        if sourceType : node.type = expected then
          match valueFound : source.lookupExpression? value with
          | none => none
          | some valueNode =>
            if valueType : valueNode.type = expected then do
              let ⟨approved⟩ ← expression value
              pure ⟨.returning rest found form sourceType valueFound valueType approved⟩
            else none
        else none
      | .expression value semicolon =>
        if notTail : (!semicolon && mode && rest.isEmpty) = false then
          if continuing : semicolon = true ∨ mode = false then
            match valueFound : source.lookupExpression? value with
            | none => none
            | some _ => do
              let ⟨approved⟩ ← expression value
              let ⟨remaining⟩ ← scan? locals caller active source expression expected fuel mode rest
              pure ⟨.discard found form notTail continuing valueFound approved remaining⟩
          else none
        else
          match _semicolon : semicolon, _mode : mode, _rest : rest with
          | false, true, [] =>
            if sourceType : node.type = expected then
              match valueFound : source.lookupExpression? value with
              | none => none
              | some valueNode =>
                if valueType : valueNode.type = expected then do
                  let ⟨approved⟩ ← expression value
                  pure ⟨.tail found form sourceType valueFound valueType approved⟩
                else none
            else none
          | _, _, _ => none
      | .block statements => do
        let ⟨inner⟩ ← scan? locals caller active source expression expected fuel false statements
        let ⟨remaining⟩ ← scan? locals caller active source expression expected fuel mode rest
        pure ⟨.block found form inner remaining⟩
      | .ifThen condition thenBody elseBody =>
        match conditionFound : source.lookupExpression? condition with
        | none => none
        | some conditionNode =>
          if conditionType : conditionNode.type = .bool then do
            let ⟨conditionSyntax⟩ ← expression condition
            let ⟨thenTree⟩ ← scan? locals caller active source expression expected fuel false thenBody
            let ⟨elseTree⟩ ← scan? locals caller active source expression expected fuel false (elseBody.getD [])
            let ⟨remaining⟩ ← scan? locals caller active source expression expected fuel mode rest
            pure ⟨.ifThen found form conditionFound conditionType conditionSyntax thenTree elseTree remaining⟩
          else none
      | .breakStmt => some ⟨.breaking rest found form⟩
      | .continueStmt => some ⟨.continuing rest found form⟩
      | .whileLoop condition statements =>
        match conditionFound : source.lookupExpression? condition with
        | none => none
        | some conditionNode =>
          if conditionType : conditionNode.type = .bool then do
            let ⟨conditionSyntax⟩ ← expression condition
            let ⟨loopTree⟩ ← scan? locals caller active source expression expected fuel false statements
            let ⟨remaining⟩ ← scan? locals caller active source expression expected fuel mode rest
            pure ⟨.whileLoop found form conditionFound conditionType conditionSyntax loopTree remaining⟩
          else none
      | .forLoop initialItems condition postItems statements =>
        match conditionFound : source.lookupExpression? condition with
        | none => none
        | some conditionNode =>
          if conditionType : conditionNode.type = .bool then do
            let ⟨initialTree⟩ ← CellAwareForHeaderAdmission.scan? source expression initialItems
            let ⟨conditionSyntax⟩ ← expression condition
            let ⟨loopTree⟩ ← scan? locals caller active source expression expected fuel false statements
            let ⟨postTree⟩ ← CellAwareForHeaderAdmission.scan? source expression postItems
            let ⟨remaining⟩ ← scan? locals caller active source expression expected fuel mode rest
            pure ⟨.forLoop found form initialTree conditionFound conditionType conditionSyntax loopTree postTree remaining⟩
          else none
      | .assignValue assignment operator rhs =>
        match declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root with
        | .error _ => none
        | .ok binder =>
          if profile : operator = .equal ∨ assignment.target.type = .word then
            match rhsFound : source.lookupExpression? rhs with
            | none => none
            | some rhsNode =>
              if rhsType : rhsNode.type = assignment.target.type then do
                let ⟨value⟩ ← expression rhs
                let ⟨remaining⟩ ← scan? locals caller active source expression expected fuel mode rest
                if bare : assignment.target.projections = [] then
                  if targetType : binder.scheme.body = assignment.target.type then
                    pure ⟨.assign found form declaration targetType profile bare rhsFound rhsType value remaining⟩
                  else none
                else
                  let ⟨route⟩ ← AcceptedProjectedAssignmentRoute.check source binder.scheme.body assignment.target.projections assignment.target.type
                  let ⟨keys⟩ ← CellAwareForHeaderAdmission.approvedKeys? expression (DataPlaceKeyOrder.sourceKeys assignment.target.projections)
                  pure ⟨.assignProjected found form declaration route profile bare keys rhsFound rhsType value remaining⟩
              else none
          else none
      | .letDecl binder (some initializer) =>
        if sourceType : node.type = .unit then
          if ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false then
            if declaration : (SourceCoreDataPlaces.declaredBinders source).filter
                (fun actual => decide (actual.id = binder.id)) = [binder] then
              match initializerFound : source.lookupExpression? initializer with
              | none => none
              | some initializerNode =>
                if valueType : initializerNode.type = binder.scheme.body then
                  if mono : binder.scheme.quantified = [] then do
                    let ⟨value⟩ ← expression initializer
                    let ⟨remaining⟩ ← scan? locals caller active source expression expected fuel mode rest
                    pure ⟨.initialized found form sourceType declaration mono ordinary initializerFound valueType value remaining⟩
                  else
                    match initializerForm : initializerNode.form with
                    | .lambda _parameters _result _body =>
                      if requirements : initializerNode.requirements = [] then
                        if coercions : initializerNode.coercions = [] then do
                          let site ← site? locals caller active source binder initializer
                          let ⟨remaining⟩ ← scan? locals caller active source expression expected fuel mode rest
                          pure ⟨.generalizedInitialized found form sourceType declaration mono ordinary initializerFound
                            initializerForm valueType requirements coercions site remaining⟩
                        else none
                      else none
                    | _ => none
                else none
            else none
          else none
        else none
      | .letDecl binder none =>
        if sourceType : node.type = .unit then
          if ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false then
            if declaration : (SourceCoreDataPlaces.declaredBinders source).filter
                (fun actual => decide (actual.id = binder.id)) = [binder] then
              if mono : binder.scheme.quantified = [] then do
                let ⟨remaining⟩ ← scan? locals caller active source expression expected fuel mode rest
                pure ⟨.uninitialized found form sourceType declaration mono ordinary remaining⟩
              else none
            else none
          else none
        else none
      | _ => none

inductive Syntax (locals : Catalog) (caller : Key) (active : Substitution)
    (source : TypedSource) (approved : ExpressionId → Prop) (expected : TypeSystem.Ty) :
    SourceSemantics.Context → Bool → List StatementId → Prop where
  | nil {context mode} (allowed : mode = false ∨ expected = .unit) :
      Syntax locals caller active source approved expected context mode []
  | returnUnit {context mode id node} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt none)
      (unit : expected = .unit) :
      Syntax locals caller active source approved expected context mode (id :: rest)
  | returning {context mode id node expression expressionNode} (rest : List StatementId)
      (found : source.lookupStatement? id = some node)
      (form : node.form = .returnStmt (some expression))
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected)
      (typed : ExpressionHasType source context expression expressionNode.type) (value : approved expression) :
      Syntax locals caller active source approved expected context mode (id :: rest)
  | tail {context id node expression expressionNode}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression false)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected)
      (typed : ExpressionHasType source context expression expressionNode.type) (value : approved expression) :
      Syntax locals caller active source approved expected context true [id]
  | generalizedInitialized {context nextContext mode id node binder initializer initializerNode parameters result body rest}
      (found : source.lookupStatement? id = some node)
      (form : node.form = .letDecl binder (some initializer))
      (declaration : (SourceCoreDataPlaces.declaredBinders source).filter (fun actual => decide (actual.id = binder.id)) = [binder])
      (polymorphic : binder.scheme.quantified ≠ [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (initializerForm : initializerNode.form = .lambda parameters result body)
      (valueType : initializerNode.type = binder.scheme.body)
      (requirements : initializerNode.requirements = []) (coercions : initializerNode.coercions = [])
      (site : Site locals caller active source binder initializer)
      (remaining : Syntax locals caller active source approved expected nextContext mode rest) :
      Syntax locals caller active source approved expected context mode (id :: rest)
  | initialized {context nextContext mode id node binder initializer initializerNode rest}
      (found : source.lookupStatement? id = some node)
      (form : node.form = .letDecl binder (some initializer))
      (member : binder ∈ SourceCoreDataPlaces.declaredBinders source)
      (mono : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (valueType : initializerNode.type = binder.scheme.body)
      (typed : ExpressionHasType source context initializer initializerNode.type)
      (value : approved initializer)
      (remaining : Syntax locals caller active source approved expected nextContext mode rest) :
      Syntax locals caller active source approved expected context mode (id :: rest)

  | uninitialized {context nextContext mode id node binder rest}
      (found : source.lookupStatement? id = some node)
      (form : node.form = .letDecl binder none)
      (member : binder ∈ SourceCoreDataPlaces.declaredBinders source)
      (mono : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (remaining : Syntax locals caller active source approved expected nextContext mode rest) :
      Syntax locals caller active source approved expected context mode (id :: rest)
  | discard {context mode id node expression expressionNode semicolon rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression semicolon)
      (notTail : (!semicolon && mode && rest.isEmpty) = false)
      (continuing : semicolon = true ∨ mode = false)
      (expressionFound : source.lookupExpression? expression = some expressionNode) (typed : ExpressionHasType source context expression expressionNode.type) (value : approved expression)
      (remaining : Syntax locals caller active source approved expected context mode rest) :
      Syntax locals caller active source approved expected context mode (id :: rest)
  | block {context mode id node statements rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
      (inner : Syntax locals caller active source approved expected context false statements)
      (remaining : Syntax locals caller active source approved expected context mode rest) :
      Syntax locals caller active source approved expected context mode (id :: rest)
  | ifThen {context mode id node condition conditionNode thenBody elseBody rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
      (conditionFound : source.lookupExpression? condition = some conditionNode) (conditionType : conditionNode.type = .bool)
      (conditionTyped : ExpressionHasType source context condition conditionNode.type)
      (conditionSyntax : approved condition)
      (thenTree : Syntax locals caller active source approved expected context false thenBody)
      (elseTree : Syntax locals caller active source approved expected context false (elseBody.getD []))
      (remaining : Syntax locals caller active source approved expected context mode rest) :
      Syntax locals caller active source approved expected context mode (id :: rest)

  | whileLoop {context mode id node condition conditionNode statements rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
      (conditionFound : source.lookupExpression? condition = some conditionNode) (conditionType : conditionNode.type = .bool)
      (conditionTyped : ExpressionHasType source context condition conditionNode.type)
      (conditionSyntax : approved condition)
      (loopTree : Syntax locals caller active source approved expected context false statements)
      (remaining : Syntax locals caller active source approved expected context mode rest) :
      Syntax locals caller active source approved expected context mode (id :: rest)
  | forLoop {context loopContext postContext mode id node initialItems condition conditionNode postItems statements rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .forLoop initialItems condition postItems statements)
      (initialTree : CellAwareForHeaderAdmission.Syntax source approved context initialItems loopContext)
      (conditionFound : source.lookupExpression? condition = some conditionNode) (conditionType : conditionNode.type = .bool)
      (conditionTyped : ExpressionHasType source loopContext condition conditionNode.type)
      (conditionSyntax : approved condition)
      (loopTree : Syntax locals caller active source approved expected loopContext false statements)
      (postTree : CellAwareForHeaderAdmission.Syntax source approved loopContext postItems postContext)
      (loopSourceTyped : ProtectedStateImperativeTypedSourceSites.Statements source loopContext statements)
      (postSourceTyped : ∃ control final, ForItemsHaveType source control loopContext postItems final)
      (remaining : Syntax locals caller active source approved expected context mode rest) :
      Syntax locals caller active source approved expected context mode (id :: rest)
  | assign {context mode id node assignment operator rhs rhsNode binder rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment operator rhs)
      (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
      (targetType : binder.scheme.body = assignment.target.type)
      (profile : operator = .equal ∨ assignment.target.type = .word)
      (bare : assignment.target.projections = [])
      (rhsFound : source.lookupExpression? rhs = some rhsNode)
      (rhsType : rhsNode.type = assignment.target.type)
      (typed : SourceAssignmentHasType source context assignment operator rhs) (value : approved rhs)
      (remaining : Syntax locals caller active source approved expected context mode rest) :
      Syntax locals caller active source approved expected context mode (id :: rest)

  | breaking {context mode id node} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .breakStmt) :
      Syntax locals caller active source approved expected context mode (id :: rest)
  | continuing {context mode id node} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .continueStmt) :
      Syntax locals caller active source approved expected context mode (id :: rest)

  | assignProjected {context mode id node assignment operator rhs rhsNode binder rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment operator rhs)
      (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
      (route : AcceptedProjectedAssignmentRoute.Route source binder.scheme.body assignment.target.projections assignment.target.type)
      (profile : operator = .equal ∨ assignment.target.type = .word)
      (projected : assignment.target.projections ≠ [])
      (keys : ∀ key ∈ DataPlaceKeyOrder.sourceKeys assignment.target.projections, approved key)
      (rhsFound : source.lookupExpression? rhs = some rhsNode)
      (rhsType : rhsNode.type = assignment.target.type)
      (typed : SourceAssignmentHasType source context assignment operator rhs)
      (value : approved rhs)
      (remaining : Syntax locals caller active source approved expected context mode rest) :
      Syntax locals caller active source approved expected context mode (id :: rest)


private theorem head_tail {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {rest : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType source control context (id :: rest) final facts) :
    ∃ middle headFacts tailFacts, StatementHasType source control context id middle headFacts ∧
      StatementsHaveType source control middle rest final tailFacts := by
  cases typed with
  | singleton head => exact ⟨_, _, _, head, .nil _ _⟩
  | cons head tail => exact ⟨_, _, _, head, tail⟩

private theorem form_at {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts} {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (typed : StatementHasType source control context id final facts) :
    Dynamic.StatementHasType.FormTyping source control context node.form final := by
  obtain ⟨actual, contains, original⟩ := Dynamic.StatementHasType.formTyping typed
  cases Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  exact original

private theorem expression_at {source : TypedSource} {context : SourceSemantics.Context}
    {id : ExpressionId} {node : ExpressionNode} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id type) : ExpressionHasType source context id node.type := by
  obtain ⟨original, contains, same⟩ := typed.stored_type
  cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  exact same ▸ typed

/-- Source child typings and lexical context extension follow the unchanged
original function typing, including every nested generalized declaration. -/
theorem Scan.syntax {locals caller active source approved expected mode statements}
    (scan : Scan locals caller active source approved expected mode statements)
    (unique : NodeOccurrencesUnique source) {control : ControlContext} (result : control.returnType = expected)
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType source control context statements final facts) :
    Syntax locals caller active source approved expected context mode statements := by
  induction scan generalizing control context final facts with
  | nil allowed => exact .nil allowed
  | breaking rest found form => exact .breaking rest found form
  | continuing rest found form => exact .continuing rest found form
  | returnUnit rest found form _ unit => exact .returnUnit rest found form unit
  | returning rest found form _ expressionFound valueType value =>
    obtain ⟨_, _, _, head, _⟩ := head_tail typed
    have original := form_at unique found head
    rw [form] at original
    cases original with
    | returnValue actual =>
      exact .returning rest found form expressionFound valueType
        (by simpa only [result, valueType] using actual) value
  | tail found form _ expressionFound valueType value =>
    obtain ⟨_, _, _, head, _⟩ := head_tail typed
    have original := form_at unique found head
    rw [form] at original
    cases original with
    | expressionValue actual =>
      exact .tail found form expressionFound valueType (expression_at unique expressionFound actual) value
  | generalizedInitialized found form _ declaration polymorphic ordinary initializerFound initializerForm valueType requirements coercions site _ ih =>
    obtain ⟨_, _, _, head, tail⟩ := head_tail typed
    have original := form_at unique found head
    rw [form] at original
    cases original with
    | letInitialized _ monomorphic _ => exact False.elim (polymorphic monomorphic)
    | letInitializedGeneralized _ _ _ _ extended =>
      exact .generalizedInitialized found form declaration polymorphic extended ordinary initializerFound
        initializerForm valueType requirements coercions site (ih result tail)
  | initialized found form _ declaration mono ordinary initializerFound valueType value _ ih =>
    obtain ⟨_, _, _, head, tail⟩ := head_tail typed
    have original := form_at unique found head
    rw [form] at original
    have member : _ ∈ SourceCoreDataPlaces.declaredBinders source :=
      (List.mem_filter.mp (declaration ▸ List.mem_singleton_self _)).1
    cases original with
    | letInitialized initial _ extended =>
      exact .initialized found form member mono extended ordinary initializerFound valueType
        (expression_at unique initializerFound initial) value (ih result tail)
    | letInitializedGeneralized quantified _ _ _ _ => exact False.elim (quantified mono)

  | uninitialized found form _ declaration mono ordinary remaining ih =>
    obtain ⟨_, _, _, head, tail⟩ := head_tail typed
    have original := form_at unique found head
    rw [form] at original
    have member : _ ∈ SourceCoreDataPlaces.declaredBinders source :=
      (List.mem_filter.mp (declaration ▸ List.mem_singleton_self _)).1
    cases original with
    | letUninitialized _ extended =>
      exact .uninitialized found form member mono extended ordinary (ih result tail)

  | discard found form notTail continuing expressionFound value _ ih =>
    obtain ⟨_,_,_,head,tail⟩ := head_tail typed
    have original := form_at unique found head
    rw [form] at original
    cases original with
    | expressionValue actual | expressionDiscard actual =>
      exact .discard found form notTail continuing expressionFound
        (expression_at unique expressionFound actual) value (ih result tail)
  | block found form _ _ innerIH remainingIH =>
    obtain ⟨_,_,_,head,tail⟩ := head_tail typed
    have original := form_at unique found head
    rw [form] at original
    cases original with
    | block inner => exact .block found form (innerIH result inner) (remainingIH result tail)
  | ifThen found form conditionFound conditionType conditionSyntax _ _ _ thenIH elseIH remainingIH =>
    obtain ⟨_,_,_,head,tail⟩ := head_tail typed
    have original := form_at unique found head
    rw [form] at original
    cases original with
    | ifWithoutElse condition thenTyped =>
      exact .ifThen found form conditionFound conditionType
        (expression_at unique conditionFound condition) conditionSyntax
        (thenIH result thenTyped) (elseIH result (.nil _ _)) (remainingIH result tail)
    | ifWithElse condition thenTyped elseTyped =>
      exact .ifThen found form conditionFound conditionType
        (expression_at unique conditionFound condition) conditionSyntax
        (thenIH result thenTyped) (elseIH result elseTyped) (remainingIH result tail)

  | whileLoop found form conditionFound conditionType conditionSyntax _ _ loopIH remainingIH =>
    obtain ⟨_, _, _, head, tail⟩ := head_tail typed
    have original := form_at unique found head
    rw [form] at original
    cases original with
    | whileLoop condition loopTyped =>
      exact .whileLoop found form conditionFound conditionType
        (expression_at unique conditionFound condition) conditionSyntax
        (loopIH (control := control.enterLoop) result loopTyped) (remainingIH result tail)
  | forLoop found form initialTree conditionFound conditionType conditionSyntax _ postTree _ loopIH remainingIH =>
    obtain ⟨_,_,_,head,tail⟩ := head_tail typed
    have original := form_at unique found head
    rw [form] at original
    cases original with
    | forLoop initialTyped conditionTyped bodyTyped postTyped =>
      exact .forLoop found form (initialTree.syntax unique initialTyped) conditionFound conditionType
        (expression_at unique conditionFound conditionTyped) conditionSyntax
        (loopIH (control := control.enterLoop) result bodyTyped) (postTree.syntax unique postTyped)
        ⟨control.enterLoop, _, _, bodyTyped⟩ ⟨control.enterLoop, _, postTyped⟩ (remainingIH result tail)
  | assign found form declaration targetType profile bare rhsFound rhsType value _ remainingIH =>
    obtain ⟨_, _, _, head, tail⟩ := head_tail typed
    have original := form_at unique found head
    rw [form] at original
    cases original with
    | assignValue assignment =>
      exact .assign found form declaration targetType profile bare rhsFound rhsType assignment value
        (remainingIH result tail)

  | assignProjected found form declaration route profile projected keys rhsFound rhsType value _ ih =>
    obtain ⟨_, _, _, head, tail⟩ := head_tail typed
    have original := form_at unique found head
    rw [form] at original
    cases original with
    | assignValue assignment =>
      exact .assignProjected found form declaration route profile projected keys rhsFound rhsType assignment value
        (ih result tail)

end Solcore.SourceSemantics.CoreLowering.CellAwareImperativeSourceBodyAdmission
