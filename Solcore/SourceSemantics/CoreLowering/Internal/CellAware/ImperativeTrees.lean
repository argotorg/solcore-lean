import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.ForLoops
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateForHeaders
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.ScopedSourceBodies
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.FaultingBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.PreparedBranching
import Solcore.SourceSemantics.CoreLowering.GenericAssignmentDiagnosticCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.LexicalBodyState
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.ReachedFormation
import Solcore.SourceSemantics.CoreLowering.GenericLexicalStatementTree
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.OrdinaryBodies
import Solcore.SourceSemantics.CoreLowering.TypedImperativeForNative
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NativeCollectors
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchArmScopes
import Solcore.SourceSemantics.CoreLowering.TypedLexicalWhileNativeCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.ScopeAssignments
import Solcore.SourceSemantics.CoreLowering.PreparedAssignmentReachedDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.ScopeStatements
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.Loops
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.LexicalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.NamedEntries
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.ScopedSourceInversion
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.StagedProjected
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateForPost
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedFlows
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.SourceForLifting
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.SourceFlowLifting

/-!
# Cell-aware imperative trees

One mixed statement tree for ordinary and generalized declarations, fallthrough, returns and scoped control, with its collectors, tree bounds, admission and Source lifting.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareImperativeSourceBodyAdmission
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareImperativeTree
/-! One mixed statement tree retains ordinary and generalized declarations,
fallthrough, returns and scoped control. Every child is a static compiler
certificate; exact marked allocation packets and native code are preserved. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareImperativeTree
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation source context)
open TypedLexicalWhile (initializedRequest sequence)

inductive Tree {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compiled : Compilation prepared named diagnostics namedCode)
    (certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (administrative : Core.Context) (reasonAt : ExpressionId → Word) :
    SourceSemantics.Context → SourceCoreLocalCell.Scope → Bool → List StatementId → TypeSystem.Ty → Ty → Expr → Prop where
  | nil {sourceContext scope mode expected type} (allowed : mode = false ∨ expected = .unit) :
      Tree prepared named compiled certificates administrative reasonAt sourceContext scope mode []
        expected type (LocalLoop.fallthrough type)
  | returnUnit {sourceContext scope mode id node} (rest : List StatementId)
      (found : (source named).lookupStatement? id = some node)
      (form : node.form = .returnStmt none) :
      Tree prepared named compiled certificates administrative reasonAt sourceContext scope mode (id :: rest)
        .unit .unit (LocalLoop.returned .unit)
  | returning {sourceContext scope mode id node expression expressionNode expected lowered} (rest : List StatementId)
      (found : (source named).lookupStatement? id = some node)
      (form : node.form = .returnStmt (some expression))
      (expressionFound : (source named).lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected)
      (typed : ExpressionHasType (source named) sourceContext expression expressionNode.type)
      (value : certificates sourceContext scope expression lowered) :
      Tree prepared named compiled certificates administrative reasonAt sourceContext scope mode (id :: rest)
        expected lowered.type (LocalLoop.returnValue lowered.type lowered.expression)
  | tail {sourceContext scope id node expression expressionNode expected lowered}
      (found : (source named).lookupStatement? id = some node)
      (form : node.form = .expression expression false)
      (expressionFound : (source named).lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected)
      (typed : ExpressionHasType (source named) sourceContext expression expressionNode.type)
      (value : certificates sourceContext scope expression lowered) :
      Tree prepared named compiled certificates administrative reasonAt sourceContext scope true [id]
        expected lowered.type (LocalLoop.returnValue lowered.type lowered.expression)
  | generalizedInitialized {sourceContext nextContext scope mode id node binder initializer initializerNode parameters result lambdaBody rest expected type lowered body childFuel}
      (found : (source named).lookupStatement? id = some node)
      (form : node.form = .letDecl binder (some initializer))
      (declaration : (SourceCoreDataPlaces.declaredBinders (source named)).filter
        (fun actual => decide (actual.id = binder.id)) = [binder])
      (polymorphic : binder.scheme.quantified ≠ [])
      (extended : BinderExtends (source named).owner sourceContext binder nextContext)
      (ordinary : (source named).inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : (source named).lookupExpression? initializer = some initializerNode)
      (initializerForm : initializerNode.form = .lambda parameters result lambdaBody)
      (valueType : initializerNode.type = binder.scheme.body)
      (requirements : initializerNode.requirements = [])
      (coercions : initializerNode.coercions = [])
      (site : CellAwareSourceBodyAdmission.Site prepared.base.locals named.signature.key [] (source named) binder initializer)
      (initial : GeneralizedLocalInitializerPackets.Receipt prepared
        (GeneralizedLocalInitializerCompilation.namedInputs compiled childFuel (childFuel + 1)
          (context prepared named) scope initializer reasonAt) site.binding [] lowered)
      (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        lowered.expression (LanguageResult.resultType lowered.type) prepared.layouts.definitions)
      (allocation : SourceCoreAllocationLayouts.Allocation prepared.layouts named.signature.key []
        (initializedRequest (source named) scope binder lowered.type))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated prepared.ancestry.layout.frame
        prepared.base.globals.length
        (prepared.layouts.allocatorAt named.signature.key [] (fun error => .sourceAllocation (reprStr error)))
        (initializedRequest (source named) scope binder lowered.type))
      (same : annotation.original = allocation.expression)
      {captured : Expr}
      (copied : SourceCoreSourceCells.copyScope (some (CallableIndexedNamedGeneration.allocator prepared named))
        (source named) scope (fun index => index)
        (CellAwareGeneralizedSnapshotCode.snapshotInner lowered.type lowered.expression annotation.expression) =
          .ok captured)
      (remaining : Tree prepared named compiled certificates administrative reasonAt
        nextContext ((binder.id, lowered.type) :: scope) mode rest expected type body) :
      Tree prepared named compiled certificates administrative reasonAt sourceContext scope mode (id :: rest)
        expected type (CellAwareGeneralizedSnapshotCode.snapshotSequence type captured body)
  | initialized {sourceContext nextContext scope mode id node binder initializer initializerNode rest expected type lowered body}
      (found : (source named).lookupStatement? id = some node)
      (form : node.form = .letDecl binder (some initializer))
      (member : binder ∈ SourceCoreDataPlaces.declaredBinders (source named))
      (mono : binder.scheme.quantified = [])
      (extended : BinderExtends (source named).owner sourceContext binder nextContext)
      (ordinary : (source named).inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : (source named).lookupExpression? initializer = some initializerNode)
      (valueType : initializerNode.type = binder.scheme.body)
      (typed : ExpressionHasType (source named) sourceContext initializer initializerNode.type)
      (value : certificates sourceContext scope initializer lowered)
      (allocation : SourceCoreAllocationLayouts.Allocation prepared.layouts named.signature.key []
        (initializedRequest (source named) scope binder lowered.type))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated prepared.ancestry.layout.frame
        prepared.base.globals.length
        (prepared.layouts.allocatorAt named.signature.key [] (fun error => .sourceAllocation (reprStr error)))
        (initializedRequest (source named) scope binder lowered.type))
      (same : annotation.original = allocation.expression)
      (remaining : Tree prepared named compiled certificates administrative reasonAt
        nextContext ((binder.id, lowered.type) :: scope) mode rest expected type body) :
      Tree prepared named compiled certificates administrative reasonAt sourceContext scope mode (id :: rest)
        expected type (sequence type lowered.expression annotation.expression body)

  | uninitialized {sourceContext nextContext scope mode id node binder rest expected type body payload}
      (found : (source named).lookupStatement? id = some node)
      (form : node.form = .letDecl binder none)
      (member : binder ∈ SourceCoreDataPlaces.declaredBinders (source named))
      (mono : binder.scheme.quantified = [])
      (extended : BinderExtends (source named).owner sourceContext binder nextContext)
      (ordinary : (source named).inputs.any (fun input => decide (input.id = binder.id)) = false)
      (projected : checked.catalog.project binder.scheme.body = .ok payload)
      (allocation : SourceCoreAllocationLayouts.Allocation prepared.layouts named.signature.key []
        (TypedLexicalControl.absentRequest (source named) scope binder payload))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated prepared.ancestry.layout.frame
        prepared.base.globals.length
        (prepared.layouts.allocatorAt named.signature.key [] (fun error => .sourceAllocation (reprStr error)))
        (TypedLexicalControl.absentRequest (source named) scope binder payload))
      (same : annotation.original = allocation.expression)
      (remaining : Tree prepared named compiled certificates administrative reasonAt
        nextContext ((binder.id, payload) :: scope) mode rest expected type body) :
      Tree prepared named compiled certificates administrative reasonAt sourceContext scope mode (id :: rest)
        expected type (.letE annotation.expression body)

  | discard {sourceContext scope mode id node expression expressionNode semicolon rest expected lowered type body}
      (found : (source named).lookupStatement? id = some node)
      (form : node.form = .expression expression semicolon)
      (notTail : (!semicolon && mode && rest.isEmpty) = false)
      (continuing : semicolon = true ∨ mode = false)
      (expressionFound : (source named).lookupExpression? expression = some expressionNode)
      (typed : ExpressionHasType (source named) sourceContext expression expressionNode.type)
      (value : certificates sourceContext scope expression lowered)
      (remaining : Tree prepared named compiled certificates administrative reasonAt
        sourceContext scope mode rest expected type body) :
      Tree prepared named compiled certificates administrative reasonAt sourceContext scope mode (id :: rest)
        expected type (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body)
  | block {sourceContext scope mode id node statements rest expected type innerCode body}
      (found : (source named).lookupStatement? id = some node)
      (form : node.form = .block statements)
      (inner : Tree prepared named compiled certificates administrative reasonAt
        sourceContext scope false statements expected type innerCode)
      (remaining : Tree prepared named compiled certificates administrative reasonAt
        sourceContext scope mode rest expected type body) :
      Tree prepared named compiled certificates administrative reasonAt sourceContext scope mode (id :: rest)
        expected type (LocalLoop.sequence type innerCode body)
  | ifThen {sourceContext scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body}
      (found : (source named).lookupStatement? id = some node)
      (form : node.form = .ifThen condition thenBody elseBody)
      (conditionFound : (source named).lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (conditionTyped : ExpressionHasType (source named) sourceContext condition conditionNode.type)
      (conditionCertificate : certificates sourceContext scope condition ⟨.bool, conditionCode⟩)
      (thenTree : Tree prepared named compiled certificates administrative reasonAt
        sourceContext scope false thenBody expected type thenCode)
      (elseTree : Tree prepared named compiled certificates administrative reasonAt
        sourceContext scope false (elseBody.getD []) expected type elseCode)
      (remaining : Tree prepared named compiled certificates administrative reasonAt
        sourceContext scope mode rest expected type body) :
      Tree prepared named compiled certificates administrative reasonAt sourceContext scope mode (id :: rest)
        expected type (LocalLoop.sequence type (LocalLoop.conditional type conditionCode thenCode elseCode) body)

  | whileLoop {sourceContext scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body escaped}
      (found : (source named).lookupStatement? id = some node)
      (form : node.form = .whileLoop condition statements)
      (conditionFound : (source named).lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (conditionTyped : ExpressionHasType (source named) sourceContext condition conditionNode.type)
      (conditionCertificate : certificates sourceContext scope condition ⟨.bool, conditionCode⟩)
      (loopTree : Tree prepared named compiled certificates administrative reasonAt
        sourceContext scope false statements expected type loopCode)
      (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.whileLoop type conditionCode loopCode escaped)
        (LanguageResult.resultType (LocalLoop.controlType type)) prepared.layouts.definitions)
      (remaining : Tree prepared named compiled certificates administrative reasonAt
        sourceContext scope mode rest expected type body) :
      Tree prepared named compiled certificates administrative reasonAt sourceContext scope mode (id :: rest)
        expected type (LocalLoop.sequence type (LocalLoop.whileLoop type conditionCode loopCode escaped) body)
  | forLoop {sourceContext loopContext postContext scope loopScope postScope mode id node initialItems condition conditionNode postItems statements rest expected type conditionCode loopCode postCode initialCode body escaped}
      (found : (source named).lookupStatement? id = some node)
      (form : node.form = .forLoop initialItems condition postItems statements)
      (initialTree : CellAwareForHeaderTree.Tree prepared named compiled certificates administrative type
        loopContext loopScope (LocalLoop.iterate type conditionCode loopCode postCode escaped)
        sourceContext scope initialItems initialCode)
      (conditionFound : (source named).lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (conditionTyped : ExpressionHasType (source named) loopContext condition conditionNode.type)
      (conditionCertificate : certificates loopContext loopScope condition ⟨.bool, conditionCode⟩)
      (loopTree : Tree prepared named compiled certificates administrative reasonAt
        loopContext loopScope false statements expected type loopCode)
      (postTree : CellAwareForHeaderTree.Tree prepared named compiled certificates administrative type
        postContext postScope (LocalLoop.fallthrough type) loopContext loopScope postItems postCode)
      (loopSourceTyped : ProtectedStateImperativeTypedSourceSites.Statements (source named) loopContext statements)
      (postSourceTyped : ∃ control final, ForItemsHaveType (source named) control loopContext postItems final)
      (nativeTyped : HasType (SourceCoreLocalCell.coreContext loopScope ++ administrative)
        (LocalLoop.iterate type conditionCode loopCode postCode escaped)
        (LanguageResult.resultType (LocalLoop.controlType type)) prepared.layouts.definitions)
      (remaining : Tree prepared named compiled certificates administrative reasonAt
        sourceContext scope mode rest expected type body) :
      Tree prepared named compiled certificates administrative reasonAt sourceContext scope mode (id :: rest)
        expected type (LocalLoop.sequence type initialCode body)
  | assign {sourceContext scope mode id node assignment operator expression rest expected type body}
      (found : (source named).lookupStatement? id = some node)
      (form : node.form = .assignValue assignment operator expression)
      (head : GenericAssignmentStatements.Head (.initial checked) (source named) sourceContext
        (certificates sourceContext) scope administrative prepared.layouts.definitions assignment operator expression)
      (bare : assignment.target.projections = [])
      (rightTyped : ExpressionHasType (source named) sourceContext expression assignment.target.type)
      (operands : AssignmentOperandDiagnostics.OperandsLaw
        (GenericAssignmentDiagnostics.OperandRep compiled.own.assignments) operator head.invalid)
      (remaining : Tree prepared named compiled certificates administrative reasonAt
        sourceContext scope mode rest expected type body) :
      Tree prepared named compiled certificates administrative reasonAt sourceContext scope mode (id :: rest)
        expected type (head.emit body (LocalLoop.controlType type))

  | assignProjected {sourceContext scope mode id node assignment operator expression rest expected type body}
      (found : (source named).lookupStatement? id = some node)
      (form : node.form = .assignValue assignment operator expression)
      (head : GenericAssignmentStatements.Head (.initial checked) (source named) sourceContext
        (certificates sourceContext) scope administrative prepared.layouts.definitions assignment operator expression)
      (projected : assignment.target.projections ≠ [])
      (rightTyped : ExpressionHasType (source named) sourceContext expression assignment.target.type)
      (site : ∀ registry, PreparedBranchingCatalogSites.AssignmentSite
        (fun site root => diagnostics.placeReason named.signature.key site root none)
        (fun site root raw => diagnostics.placeReason named.signature.key site root (some raw))
        registry (GenericAssignmentDiagnostics.OperandRep compiled.own.assignments) head)
      (remaining : Tree prepared named compiled certificates administrative reasonAt
        sourceContext scope mode rest expected type body) :
      Tree prepared named compiled certificates administrative reasonAt sourceContext scope mode (id :: rest)
        expected type (head.emit body (LocalLoop.controlType type))

  | breaking {sourceContext scope mode id node expected type} (rest : List StatementId)
      (found : (source named).lookupStatement? id = some node)
      (form : node.form = .breakStmt) :
      Tree prepared named compiled certificates administrative reasonAt sourceContext scope mode (id :: rest)
        expected type (LocalLoop.breaking type)
  | continuing {sourceContext scope mode id node expected type} (rest : List StatementId)
      (found : (source named).lookupStatement? id = some node)
      (form : node.form = .continueStmt) :
      Tree prepared named compiled certificates administrative reasonAt sourceContext scope mode (id :: rest)
        expected type (LocalLoop.continuing type)

end Solcore.SourceSemantics.CoreLowering.CellAwareImperativeTree
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareImperativeCollectors
/-! The native body collector follows the actual named compiler and its
marked lexical allocations. Source typing supplies context extension; the
accepted initializer supplies the complete ordered candidate bundle. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareImperativeCollectors
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation source context)
open CompatibleEncoding (bind_ok)
open GeneralizedLocalInitializerCompilation (namedInputs)

private theorem read_found {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource}
    {id : StatementId} {node : StatementNode} {type : Ty}
    (accepted : SourceCoreCompatibleDataExpressions.readStatement checked source id = .ok (node, type)) :
    source.lookupStatement? id = some node := by
  unfold SourceCoreCompatibleDataExpressions.readStatement at accepted
  by_cases owner : id.occurrence.owner ≠ source.owner
  · simp [owner, throw, bind, Except.bind] at accepted
  · simp only [owner, ↓reduceIte, bind, Except.bind, pure, Except.pure] at accepted
    cases found : source.lookupStatement? id with
    | none => simp [found] at accepted
    | some actual =>
      simp only [found] at accepted
      obtain ⟨projected, _, same⟩ := bind_ok accepted
      cases same
      rfl

private theorem ensure_same {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

private theorem computation_child {definitions : DataEnvironment}
    {context : Core.Context} {output nativeType : Ty} {computation body : Expr}
    (typed : HasType context (LanguageResult.bind output computation body) nativeType definitions) :
    ∃ childType, HasType context computation childType definitions := by
  cases typed with | caseE child _ _ => exact ⟨_, child⟩


private theorem while_condition {definitions : DataEnvironment} {context : Core.Context}
    {type result : Ty} {condition body : Expr} {reason : Word}
    (typed : HasType context (LocalLoop.whileLoop type condition body reason) result definitions) :
    ∃ childType, HasType context condition childType definitions := by
  cases typed with
  | letE allocation installed =>
    cases installed with
    | letE written invoked =>
      cases written with
      | storeCell reference closure =>
        cases closure with
        | inRight unitWF raw =>
          cases raw with
          | lambda parameterWF resultWF loop =>
            obtain ⟨_, shifted⟩ := computation_child loop
            exact ⟨_, TypedLexicalWhile.Native.remove_front (TypedLexicalWhile.Native.remove_front shifted)⟩

private theorem for_condition {definitions : DataEnvironment} {context : Core.Context}
    {type result : Ty} {condition body post : Expr} {reason : Word}
    (typed : HasType context (LocalLoop.iterate type condition body post reason) result definitions) :
    ∃ childType, HasType context condition childType definitions := by
  cases typed with
  | letE allocation installed =>
    cases installed with
    | letE written invoked =>
      cases written with
      | storeCell reference closure =>
        cases closure with
        | inRight unitWF raw =>
          cases raw with
          | lambda parameterWF resultWF loop =>
            obtain ⟨_, shifted⟩ := computation_child loop
            exact ⟨_, TypedLexicalWhile.Native.remove_front (TypedLexicalWhile.Native.remove_front shifted)⟩

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  (compiled : Compilation prepared named diagnostics namedCode)
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {approved : ExpressionId → Prop} {administrative : Core.Context} {reasonAt : ExpressionId → Word}
  {policy : SourceCoreLoops.Policy}

/-- Only finite static expression and candidate profiles are inputs. All
compiler actions and native child typing are recovered from the accepted body. -/
theorem collected
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    (unique : NodeOccurrencesUnique (source named))
    (assignmentsPrepared : ∃ first, SourceCoreAssignmentFaultSites.prepare (source named) first = .ok compiled.own.assignments)
    (assignmentPolicy : ∀ fuel scope site assignment operator rhs output next reasonAt,
      SourceCoreLoops.assignValue policy fuel (source named) scope site assignment operator rhs output next reasonAt =
      SourceCoreCompatibleDataPlaces.lower (.initial checked) checked.signatures policy.lowerExpression
        fuel (source named) scope site assignment operator (some rhs) output next reasonAt
        (diagnostics.placeReason named.signature.key site assignment.target.root none)
        (GenericAssignmentDiagnostics.token compiled.own.assignments site assignment.target.root operator)
        (fun type => diagnostics.placeReason named.signature.key site assignment.target.root (some type)))
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (expressionPolicy : policy.lowerExpression =
      SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram
        ((CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key [])
        prepared.base.sourceProgram.signatures prepared.base.locals compiled.parents compiled.own.assignments
        diagnostics (context prepared named) prepared.base.callableContext none none)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder (source named) scope binder = SourceCoreCompatibleDataExpressions.lowerBinder checked (source named) scope binder)
    (allocationPolicy : policy.sourceCells = some (CallableIndexedNamedGeneration.allocator prepared named))
    (profiles : ∀ {scope binder initializer}
      (site : CellAwareSourceBodyAdmission.Site prepared.base.locals named.signature.key []
        (source named) binder initializer) childFuel,
      ∀ candidate ∈ site.binding.atContext [],
        Nonempty (GeneralizedLocalInitializerPackets.BindingProfile
          (GeneralizedLocalInitializerCompilation.namedInputs compiled childFuel (childFuel + 1)
            (context prepared named) scope initializer reasonAt) site.binding candidate))
    (bodyProfiles : ∀ {scope binder initializer}
      (site : CellAwareSourceBodyAdmission.Site prepared.base.locals named.signature.key []
        (source named) binder initializer) childFuel,
      ∀ candidate ∈ site.binding.atContext [], Nonempty (GeneralizedLocalBodyProfile.Profile
        (namedInputs compiled childFuel (childFuel + 1) (context prepared named) scope initializer reasonAt).locals
        (namedInputs compiled childFuel (childFuel + 1) (context prepared named) scope initializer reasonAt).current.owner
        candidate.source initializer))
    (children : ∀ sourceContext,
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations (source named) scope sourceContext →
      approved id → (source named).lookupExpression? id = some node →
      ExpressionHasType (source named) sourceContext id node.type →
      policy.lowerExpression fuel (source named) scope id reasonAt = .ok lowered →
      ∀ {nativeType}, HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        lowered.expression nativeType prepared.layouts.definitions → certificates sourceContext scope id lowered)
    {sourceContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : CellAwareImperativeSourceBodyAdmission.Syntax prepared.base.locals named.signature.key []
      (source named) approved expected sourceContext mode statements)
    (declarations : CompatibleExpressionReads.ScopeDeclarations (source named) scope sourceContext)
    (sourceSignatures : sourceContext.signatures = checked.signatures)
    {fuel : Nat} {type : Ty} {code : Expr} {escaped : Word} {nativeType : Ty}
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel (source named) scope statements
      type reasonAt mode escaped = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType prepared.layouts.definitions) :
    CellAwareImperativeTree.Tree prepared named compiled certificates administrative reasonAt
      sourceContext scope mode statements expected type code := by
  induction syntaxTree generalizing scope fuel code nativeType with
  | nil allowed =>
    have same : (Except.ok (LocalLoop.fallthrough type) : Except SourceCoreBasic.Error Expr) = Except.ok code := by simpa only [SourceCoreLoops.lowerFlowStatementsWithPolicy] using accepted
    cases same
    exact .nil allowed
  | @returnUnit sourceContext mode id node rest found form unit =>
    cases unit
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checkedType, first, accepted⟩ := bind_ok accepted
      cases checkedType
      obtain ⟨checkedType, second, accepted⟩ := bind_ok accepted
      cases checkedType
      have same := (ensure_same first).trans (ensure_same second).symm
      subst type
      simp only [first, bind, Except.bind, pure, Except.pure] at accepted
      cases accepted
      exact .returnUnit rest found form
  | @returning sourceContext mode id node expression expressionNode rest found form expressionFound valueType typed value =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checkedType, _, accepted⟩ := bind_ok accepted
      cases checkedType
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨checkedType, sameType, accepted⟩ := bind_ok accepted
      cases checkedType
      have same := ensure_same sameType
      subst type
      cases accepted
      obtain ⟨_, childTyped⟩ := computation_child nativeTyped
      exact .returning rest found form expressionFound valueType typed
        (children sourceContext declarations value expressionFound typed generated childTyped)
  | @tail sourceContext id node expression expressionNode found form expressionFound valueType typed value =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      simp only [Bool.not_false, Bool.and_self, List.isEmpty_nil, ↓reduceIte] at accepted
      obtain ⟨checkedType, _, accepted⟩ := bind_ok accepted
      cases checkedType
      obtain ⟨checkedType, sameType, accepted⟩ := bind_ok accepted
      cases checkedType
      have same := ensure_same sameType
      subst type
      cases accepted
      obtain ⟨_, childTyped⟩ := computation_child nativeTyped
      exact .tail found form expressionFound valueType typed
        (children sourceContext declarations value expressionFound typed generated childTyped)
  | @generalizedInitialized sourceContext nextContext mode id node binder initializer initializerNode parameters result body rest found form declaration polymorphic extended ordinary initializerFound initializerForm valueType requirements coercions site remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checkedType, _, accepted⟩ := bind_ok accepted
      cases checkedType
      obtain ⟨payload, _projected, accepted⟩ := bind_ok accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨checkedType, sameType, accepted⟩ := bind_ok accepted
      cases checkedType
      have same := ensure_same sameType
      subst payload
      obtain ⟨tailCode, generatedTail, accepted⟩ := bind_ok accepted
      have generalizedBinder : binder.scheme.quantified.isEmpty = false := by
        cases quantified : binder.scheme.quantified with
        | nil => exact absurd quantified polymorphic
        | cons _ _ => rfl
      simp only [generalizedBinder, Bool.false_eq_true, ↓reduceIte, SourceCoreSourceCells.letInitializedSnapshot,
        allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      obtain ⟨captured, copied, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ :=
        CallableIndexedAllocationCompletion.accepted_receipts (fun error => .sourceAllocation (reprStr error)) generatedAllocation
      have actualGenerated := expressionPolicy ▸ generated
      obtain ⟨childFuel, fuelEq, binding, located, ⟨initial⟩⟩ :=
        GeneralizedLocalInitializerCompilation.of_named_contextual compiled record
          initializerFound initializerForm site.selected actualGenerated
      have sameBinding : binding = site.binding := by
        rw [site.selectedBinder] at located
        exact Except.ok.inj (located.symm.trans site.located)
      subst binding
      subst fuel
      obtain ⟨initial⟩ := GeneralizedLocalInitializerPackets.of_receipt prepared initial
        (profiles site childFuel) (bodyProfiles site childFuel) rfl rfl rfl rfl rfl rfl rfl
      obtain ⟨⟨_, childTyped⟩, tailTyped⟩ := CellAwareGeneralizedSnapshotTyping.snapshot_children allocation annotation
        same copied (fun _ _ _ found => CellAwareGeneralizedSnapshotTyping.scope_cell found) nativeTyped
      have tail := ih
        (CellAwareNativeBodyCollectors.scope_generalized lowered.type declarations declaration polymorphic extended)
        (by cases extended; exact sourceSignatures) generatedTail tailTyped
      exact .generalizedInitialized found form declaration polymorphic extended ordinary
        initializerFound initializerForm valueType requirements coercions site initial
        (initial.typed childTyped) allocation annotation same copied tail
  | @initialized sourceContext nextContext mode id node binder initializer initializerNode rest found form member mono extended ordinary initializerFound valueType typed value remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checkedType, _, accepted⟩ := bind_ok accepted
      cases checkedType
      obtain ⟨payload, _projected, accepted⟩ := bind_ok accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨checkedType, sameType, accepted⟩ := bind_ok accepted
      cases checkedType
      have same := ensure_same sameType
      subst payload
      obtain ⟨tailCode, generatedTail, accepted⟩ := bind_ok accepted
      simp only [mono, List.isEmpty_nil, ↓reduceIte] at accepted
      simp only [SourceCoreSourceCells.letInitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ :=
        CallableIndexedAllocationCompletion.accepted_receipts (fun error => .sourceAllocation (reprStr error)) generatedAllocation
      obtain ⟨_, childTyped⟩ := computation_child nativeTyped
      have tail := ih (CompatibleMatchArmScopes.scope_bind lowered.type declarations member extended)
        (by cases extended; exact sourceSignatures) generatedTail (TypedLexicalWhile.Native.initialized_child allocation annotation same nativeTyped)
      exact .initialized found form member mono extended ordinary initializerFound valueType typed
        (children sourceContext declarations value initializerFound typed generated childTyped)
        allocation annotation same tail

  | @uninitialized sourceContext nextContext mode id node binder rest found form member mono extended ordinary remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checkedType, _, accepted⟩ := bind_ok accepted
      cases checkedType
      obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
      obtain ⟨tailCode, generatedTail, accepted⟩ := bind_ok accepted
      simp only [SourceCoreSourceCells.letUninitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ :=
        CallableIndexedAllocationCompletion.accepted_receipts (fun error => .sourceAllocation (reprStr error)) generatedAllocation
      have tail := ih (CompatibleMatchArmScopes.scope_bind payload declarations member extended)
        (by cases extended; exact sourceSignatures) generatedTail (TypedLexicalWhile.Native.absent_child allocation annotation same nativeTyped)
      exact .uninitialized found form member mono extended ordinary
        (CompatibleStatementBindings.binder_projected (binderPolicy scope binder mono ▸ projected))
        allocation annotation same tail

  | @discard sourceContext mode id node expression expressionNode semicolon rest found form notTail continuing expressionFound typed value remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      simp only [notTail, Bool.false_eq_true, ↓reduceIte] at accepted
      cases semicolon <;> simp only [Bool.false_eq_true, ↓reduceIte] at accepted
      all_goals
        obtain ⟨checked, _, accepted⟩ := bind_ok accepted
        cases checked
        obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
        cases accepted
        obtain ⟨_, tailTyped⟩ := TypedLexicalWhile.Native.discard_child nativeTyped
        obtain ⟨_, childTyped⟩ := computation_child nativeTyped
        exact .discard found form notTail continuing expressionFound typed
          (children sourceContext declarations value expressionFound typed generated childTyped)
          (ih declarations sourceSignatures generatedBody tailTyped)
  | @block sourceContext mode id node statements rest found form inner remaining innerIH restIH =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨innerCode, generatedInner, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨_, headTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      exact .block found form (innerIH declarations sourceSignatures generatedInner headTyped) (restIH declarations sourceSignatures generatedBody tailTyped)
  | @ifThen sourceContext mode id node condition conditionNode thenBody elseBody rest found form conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax remaining thenIH elseIH restIH =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨conditionCode, generatedCondition, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedCondition, accepted⟩ := bind_ok accepted
      cases checked
      have conditionTypeEq := ensure_same checkedCondition
      rcases conditionCode with ⟨native, code⟩
      dsimp only at conditionTypeEq
      subst native
      obtain ⟨thenCode, generatedThen, accepted⟩ := bind_ok accepted
      cases elseBody with
      | none =>
        simp only [bind, Except.bind, pure, Except.pure] at accepted
        obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
        cases accepted
        have generatedElse : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel (source named) scope [] type reasonAt false escaped =
            .ok (LocalLoop.fallthrough type) := by cases fuel <;> rfl
        obtain ⟨⟨_, branchTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
        obtain ⟨⟨_, thenTyped⟩, ⟨_, elseTyped⟩⟩ := TypedLexicalWhile.Native.conditional_children branchTyped
        obtain ⟨_, childTyped⟩ := computation_child branchTyped
        exact .ifThen found form conditionFound conditionType typed
          (children sourceContext declarations conditionSyntax conditionFound typed generatedCondition childTyped)
          (thenIH declarations sourceSignatures generatedThen thenTyped) (elseIH declarations sourceSignatures generatedElse elseTyped) (restIH declarations sourceSignatures generatedBody tailTyped)
      | some statements =>
        obtain ⟨elseCode, generatedElse, accepted⟩ := bind_ok accepted
        obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
        cases accepted
        obtain ⟨⟨_, branchTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
        obtain ⟨⟨_, thenTyped⟩, ⟨_, elseTyped⟩⟩ := TypedLexicalWhile.Native.conditional_children branchTyped
        obtain ⟨_, childTyped⟩ := computation_child branchTyped
        exact .ifThen found form conditionFound conditionType typed
          (children sourceContext declarations conditionSyntax conditionFound typed generatedCondition childTyped)
          (thenIH declarations sourceSignatures generatedThen thenTyped) (elseIH declarations sourceSignatures generatedElse elseTyped) (restIH declarations sourceSignatures generatedBody tailTyped)

  | @whileLoop sourceContext mode id node condition conditionNode statements rest found form conditionFound conditionType typed conditionSyntax loopSyntax remaining loopIH restIH =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨conditionCode, generatedCondition, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedCondition, accepted⟩ := bind_ok accepted
      cases checked
      have sameType := ensure_same checkedCondition
      rcases conditionCode with ⟨native, code⟩
      dsimp only at sameType
      subst native
      obtain ⟨loopCode, generatedLoop, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨_, loopTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      obtain ⟨_, childTyped⟩ := while_condition loopTyped
      obtain ⟨⟨_, loopBodyTyped⟩, loopTyped⟩ := TypedLexicalWhile.Native.while_body loopTyped
      exact .whileLoop found form conditionFound conditionType typed
        (children sourceContext declarations conditionSyntax conditionFound typed generatedCondition childTyped)
        (loopIH declarations sourceSignatures generatedLoop loopBodyTyped)
        loopTyped
        (restIH declarations sourceSignatures generatedBody tailTyped)

  | @forLoop sourceContext loopContext postContext mode id node initialItems condition conditionNode postItems statements rest
      found form initialSyntax conditionFound conditionType typed conditionSyntax loopSyntax postSyntax loopSourceTyped postSourceTyped remaining loopIH restIH =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checkedType, _, accepted⟩ := bind_ok accepted
      cases checkedType
      obtain ⟨initialCode, generatedInitial, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨_, initialTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      let nextReceipt : SourceCoreLocalCell.Scope → Expr → Prop := fun loopScope terminal =>
        ∃ conditionCode loopCode postCode postScope,
          terminal = LocalLoop.iterate type conditionCode loopCode postCode escaped ∧
          certificates loopContext loopScope condition ⟨.bool, conditionCode⟩ ∧
          CellAwareImperativeTree.Tree prepared named compiled certificates administrative reasonAt
            loopContext loopScope false statements expected type loopCode ∧
          CellAwareForHeaderTree.Tree prepared named compiled certificates administrative type
            postContext postScope (LocalLoop.fallthrough type) loopContext loopScope postItems postCode ∧
          HasType (SourceCoreLocalCell.coreContext loopScope ++ administrative)
            (LocalLoop.iterate type conditionCode loopCode postCode escaped)
            (LanguageResult.resultType (LocalLoop.controlType type)) prepared.layouts.definitions
      have origin := AssignmentDiagnosticOrigins.ForOriginFor.start (tracked := true) found form
      obtain ⟨loopScope, terminal, completed, initialTree⟩ := CellAwareForHeaderCollectors.collected compiled
        unique assignmentsPrepared assignmentPolicy binderPolicy allocationPolicy children
        (continuation := nextReceipt)
        (fun loopScope terminal loopDeclarations accepted _nativeType nativeTyped => by
          obtain ⟨conditionCode, generatedCondition, accepted⟩ := bind_ok accepted
          obtain ⟨checkedType, checkedCondition, accepted⟩ := bind_ok accepted
          cases checkedType
          have sameType := ensure_same checkedCondition
          rcases conditionCode with ⟨native, code⟩
          dsimp only at sameType
          subst native
          obtain ⟨loopCode, generatedLoop, accepted⟩ := bind_ok accepted
          obtain ⟨postCode, generatedPost, accepted⟩ := bind_ok accepted
          cases accepted
          obtain ⟨_, conditionNative⟩ := for_condition nativeTyped
          obtain ⟨⟨_, loopNative⟩, ⟨_, postNative⟩, loopTyped⟩ := TypedImperativeFor.Native.iterate_children nativeTyped
          obtain ⟨postScope, postTerminal, postSame, postTree⟩ := CellAwareForHeaderCollectors.collected compiled
            unique assignmentsPrepared assignmentPolicy binderPolicy allocationPolicy children
            (continuation := fun _ terminal => terminal = LocalLoop.fallthrough type)
            (fun _ _ _ accepted _ _ => Except.ok.inj accepted.symm)
            postSyntax loopDeclarations (initialSyntax.signatures.trans sourceSignatures) origin.post_origin generatedPost postNative
          subst postTerminal
          exact ⟨code, loopCode, postCode, postScope, rfl,
            children loopContext loopDeclarations conditionSyntax conditionFound typed generatedCondition conditionNative,
            loopIH loopDeclarations (initialSyntax.signatures.trans sourceSignatures) generatedLoop loopNative, postTree, loopTyped⟩)
        initialSyntax declarations sourceSignatures origin.header generatedInitial initialTyped
      obtain ⟨conditionCode, loopCode, postCode, postScope, rfl, conditionCertificate, loopTree, postTree, loopTyped⟩ := completed
      exact .forLoop found form initialTree conditionFound conditionType typed conditionCertificate
        loopTree postTree loopSourceTyped postSourceTyped loopTyped (restIH declarations sourceSignatures generatedBody tailTyped)

  | @assign sourceContext mode id node assignment operator rhs rhsNode binder rest found form declaration targetType profile bare rhsFound rhsType assignmentTyped value remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checkedType, _, accepted⟩ := bind_ok accepted
      cases checkedType
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      rw [assignmentPolicy] at accepted
      obtain ⟨_projections, writable, rightTyped, runtimeProfile⟩ :=
        ScopedSourceForItemsAdmission.assignment_facts declaration targetType bare assignmentTyped
      obtain ⟨actualBinder, preparedPlace, index, lowered, _binding, _rootType, _rawView, _slot,
        _layout, generated, _sameType, _profile, codeEq⟩ := CompatibleBareAssignment.of_lower bare accepted
      obtain ⟨_, rhsNative⟩ := (CallableIndexedOwnedPreparedNativeAssignmentChildren.execute_children
        (codeEq ▸ nativeTyped)).1
      have child : certificates sourceContext scope rhs lowered :=
        children sourceContext declarations value rhsFound (rhsType.symm ▸ rightTyped) generated rhsNative
      obtain ⟨head, emitted, token⟩ := GenericAssignmentStatements.Head.of_lower_bare_with_token
        (administrative := administrative) (definitions := prepared.layouts.definitions)
        bare unique writable rightTyped runtimeProfile (fun actual acceptedRight => by
          have same : actual = lowered := Except.ok.inj (acceptedRight.symm.trans generated)
          subst actual
          exact ⟨rhsNode, rhsFound, child⟩) accepted
      have tailTyped := TypedImperative.Native.execute_continuation (emitted ▸ nativeTyped)
      obtain ⟨first, tablePrepared⟩ := assignmentsPrepared
      have rawProfile : operator = .equal ∨ assignment.target.type = .word ∨ assignment.target.type = .integer ∧ operator.wordOnly = false := by
        rcases profile with equal | word
        · exact .inl equal
        · exact .inr (.inl word)
      have operands := GenericAssignmentDiagnostics.prepared_operands tablePrepared
        (lookupStatement?_sound found).1 (.statement form) rawProfile
      rw [(lookupStatement?_sound found).2, ← token] at operands
      rw [emitted]
      exact .assign found form head bare rightTyped operands (ih declarations sourceSignatures generatedBody tailTyped)

  | @assignProjected sourceContext mode id node assignment operator rhs rhsNode binder rest found form declaration route profile projected keys rhsFound rhsType assignmentTyped value remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checkedType, _, accepted⟩ := bind_ok accepted
      cases checkedType
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      rw [assignmentPolicy] at accepted
      obtain ⟨sourceTyped, writable, rightTyped, runtimeProfile⟩ :=
        ScopedSourceForItemsAdmission.projected_assignment_facts unique declaration route assignmentTyped
      obtain ⟨head, emitted, token, preparedAt⟩ :=
        CallableIndexedOwnedPreparedNativeAssignmentHeadCollectors.Head.of_lower_with_raw_occurrences
          unique sourceSignatures sourceTyped writable rightTyped runtimeProfile
          (certificate := certificates sourceContext)
          (fun child lowered member generated raw => by
            obtain ⟨_, native⟩ := raw
            rcases List.mem_cons.mp member with same | member
            · subst child
              exact ⟨rhsNode, rhsFound, children sourceContext declarations value rhsFound
                (rhsType.symm ▸ rightTyped) generated native⟩
            · obtain ⟨node, found, childTyped⟩ := route.key_typed unique (sourceTyped binder declaration) member
              exact ⟨node, found, children sourceContext declarations (keys _ member) found childTyped generated native⟩)
          accepted nativeTyped
      have tailTyped := TypedImperative.Native.execute_continuation (emitted ▸ nativeTyped)
      obtain ⟨first, tablePrepared⟩ := assignmentsPrepared
      have rawProfile : operator = .equal ∨ assignment.target.type = .word ∨ assignment.target.type = .integer ∧ operator.wordOnly = false := by
        rcases profile with equal | word
        · exact .inl equal
        · exact .inr (.inl word)
      have operands := GenericAssignmentDiagnostics.prepared_operands tablePrepared
        (lookupStatement?_sound found).1 (.statement form) rawProfile
      rw [(lookupStatement?_sound found).2, ← token] at operands
      rw [emitted]
      exact .assignProjected found form head projected rightTyped
        (fun registry => CallableIndexedOwnedPreparedBranchingCatalogSites.assignment_site
          (.statement found form) sourceSignatures preparedAt operands registry)
        (ih declarations sourceSignatures generatedBody tailTyped)

  | breaking rest found form =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checkedType, _, accepted⟩ := bind_ok accepted
      cases checkedType
      cases accepted
      exact .breaking rest found form
  | continuing rest found form =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checkedType, _, accepted⟩ := bind_ok accepted
      cases checkedType
      cases accepted
      exact .continuing rest found form

end Solcore.SourceSemantics.CoreLowering.CellAwareImperativeCollectors
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareImperativeTreeBounds
/-! Ordinary and generalized declarations compose in the actual compiled
lexical body. Successful children retain descriptor authority before allocation;
failed children retain the reached heap without allocating a new cell. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareImperativeTreeBounds
open Core Frontend SourceInference CompatibleEquality GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post restore_post)
open CallableIndexedOwnedAdmittedStagedTerminalStatements (Head control)
open CallableIndexedNamedGeneration (source)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (bindings : ProtectedStateTransition.Bindings protocol)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  (functions : FunctionModel whole.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions whole.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial whole.compatible.checked).registry receiving)
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  (compiled : CallableIndexedNamedGeneration.Compilation whole.indexed named diagnostics namedCode)
  (record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan named.signature.key = .ok named.specialized)
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) (GeneralizedLocalInstanceValues.model whole.indexed)))
  {faults : RecursiveStageMeaning.FaultRep}
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
  (operandIncluded : ∀ reason token,
    GenericAssignmentDiagnostics.OperandRep compiled.own.assignments reason token → faults (.semantic reason) token)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations whole.compatible.checked.catalog functions identities)
  (assignmentDiagnostics : PreparedAssignmentReachedDiagnostics.Ready (values := .initial whole.compatible.checked)
    functions protocol (source named)
    (fun site root => diagnostics.placeReason named.signature.key site root none)
    (fun site root raw => diagnostics.placeReason named.signature.key site root (some raw))
    receiving (fun reason token => faults (.semantic reason) token))
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}

private theorem head_typed {context : SourceSemantics.Context} {id : StatementId} {rest : List StatementId}
    (typed : ProtectedStateImperativeTypedSourceSites.Statements (source named) context (id :: rest)) :
    ∃ control final facts, StatementHasType (source named) control context id final facts := by
  obtain ⟨control, final, facts, typed⟩ := typed
  cases typed with
  | singleton head => exact ⟨control, _, _, head⟩
  | cons head _ => exact ⟨control, _, _, head⟩

variable
  (booleans : ∀ {mapping world sourceValue nativeValue},
    (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions).Represents mapping world .bool sourceValue nativeValue .bool →
    ∃ truth, sourceValue = .bool truth ∧ nativeValue = .bool truth)
  (unitValue : ∀ mapping world, (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions).Represents mapping world .unit .unit .unit .unit)

include record bindings transport extension registered operandIncluded faithful observations assignmentDiagnostics booleans unitValue in
theorem preserves {budget : Nat}
    (children : ∀ context, Dynamic.SourceRuntimeValid program context (source named) →
      invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      CellAwareScopeExpressionBounds.PreservesBelow bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named registry invocation
      (certificates context) faults budget)
    (sourceEq : invocation.source = source named)
    {administrative : Core.Context} {reasonAt : ExpressionId → Word}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : CellAwareImperativeTree.Tree whole.indexed named compiled certificates administrative reasonAt
      context scope mode statements expected type code)
    (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed named reasonAt) :
    CellAwareScopeFlowBounds.PreservesAtMost bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
      administrative scope mode statements expected type code budget := by
  induction tree with
  | @generalizedInitialized context nextContext scope mode id node binder initializer initializerNode parameters result lambdaBody rest expected type lowered body childFuel
      found form declaration polymorphic extended ordinary _initializerFound _initializerForm _valueType _requirements _coercions site initialReceipt nativeTyped allocation annotation same captured copied remaining ih =>
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready
      finalContext outcome after trace
    have unique := runtime.graph.nodeOccurrencesUnique
    obtain ⟨tailSize, copies, snapshotHeap, function, location, bound, sameSize, snapshot, captures, allocated,
        remainingTrace⟩ :=
      CellAwareGeneralizedSourceInversion.generalized (by simpa only [sourceEq] using unique)
        (by simpa only [sourceEq] using found) form polymorphic
        (by simpa only [sourceEq] using extended) trace
    have snapshotNamed : Dynamic.EnvironmentCopies (source named) environment before copies snapshotHeap := by
      simpa only [sourceEq] using snapshot
    have capturesNamed : Dynamic.GeneralizedClosureCaptures context (source named) copies binder initializer function := by
      simpa only [sourceEq] using captures
    obtain ⟨control, next, facts, headTyped⟩ := head_typed sourceTyped
    have functionTyped := CellAwareGeneralizedSourceInversion.captured_wellTyped runtime (snapshotNamed.agrees locals)
      headTyped
      found form polymorphic capturesNamed
    have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
    obtain ⟨values, marker, copiedStore, copiedMap, copiedWorld, agreement, _smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
        preserved, effect, nextAuthority, reached, related, nextAdmitted, nextPhysical, locationEq, nativeEq⟩ :=
      CellAwareNamedGeneralizedPrefix.complete bridge compiled record site initialReceipt issuer declaration polymorphic extended
        ordinary nativeTyped allocation annotation same copied producer bindings registered environments heaps locals agrees
        actualTyped initial admitted authority physical ready snapshotNamed capturesNamed functionTyped allocated type body
    have nextReady : ProtectedStateTransition.CellAllocation.ReadyAt producer nextPhysical.location nextPhysical.native := by
      intro index current stored
      have previous := ready current (by simpa only [locationEq, nativeEq] using stored)
      simpa only [locationEq, nativeEq] using previous
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, finalFrame, metadata, finalEffect, tailState, tailRelated, post⟩ :=
      ih _ tailWithin nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
        (runtime.transport (.ofBinderExtends extended))
        ((Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers)
        ((Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger)
        (ProtectedStateImperativeStatementSuffixTyping.let_decl unique sourceTyped found form extended)
        reached nextAdmitted nextAuthority nextPhysical owner (sameLocation.trans locationEq.symm) nextReady remainingTrace
    let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (id := binder.id) (type := lowered.type)
      (value := .cellRef (OptionalCell.cellType lowered.type) (copiedStore.length + 2)) tailState
    refine ⟨value, finalStore, finalMap, finalWorld, agreement.wrap evaluated, represented, finalHeaps,
      effect.maps.trans maps, effect.worlds.trans worlds, preserved.trans finalFrame,
      effect.metadata.trans metadata, effect.trans finalEffect, finalState,
      protocol.trans related (protocol.trans tailRelated (bindings.restore_related
        (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := binder.id) (type := lowered.type)
        (value := .cellRef (OptionalCell.cellType lowered.type) (copiedStore.length + 2)) tailState)), ?_⟩
    exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (copiedStore.length + 2)) tailState post

  | @uninitialized context nextContext scope mode id node binder rest expected type body payload
      found form member mono extended ordinary projected allocation annotation same remaining ih =>
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready
      finalContext outcome after trace
    have unique := runtime.graph.nodeOccurrencesUnique
    obtain ⟨tailSize, location, bound, sameSize, allocated, remainingTrace⟩ :=
      CallableIndexedOwnedPreparedStagedScopedLexicalSourceInversion.absent
        (by simpa only [sourceEq] using unique) (by simpa only [sourceEq] using found) form
        (by simpa only [sourceEq] using extended) trace
    have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
    obtain ⟨marker, agreement, _smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
        preserved, effect, nextAuthority, reached, related, nextAdmitted, nextPhysical, locationEq, nativeEq⟩ :=
      CellAwareNamedAbsentPrefix.complete bridge mono member extended ordinary allocation annotation same producer registered
        projected environments heaps locals agrees actualTyped initial admitted authority physical
        (ready initial physical.read) allocated body
    have nextReady : ProtectedStateTransition.CellAllocation.ReadyAt producer nextPhysical.location nextPhysical.native := by
      intro index current stored
      have previous := ready current (by simpa only [locationEq, nativeEq] using stored)
      simpa only [locationEq, nativeEq] using previous
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, finalFrame, metadata, finalEffect, tailState, tailRelated, post⟩ :=
      ih _ tailWithin nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
        (runtime.transport (.ofBinderExtends extended))
        ((Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers)
        ((Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger)
        (ProtectedStateImperativeStatementSuffixTyping.let_decl unique sourceTyped found form extended)
        reached nextAdmitted nextAuthority nextPhysical owner (sameLocation.trans locationEq.symm) nextReady remainingTrace
    let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (id := binder.id) (type := payload)
      (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState
    refine ⟨value, finalStore, finalMap, finalWorld, agreement.wrap evaluated, represented, finalHeaps,
      effect.maps.trans maps, effect.worlds.trans worlds, preserved.trans finalFrame,
      effect.metadata.trans metadata, effect.trans finalEffect, finalState,
      protocol.trans related (protocol.trans tailRelated (bindings.restore_related
        (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := binder.id) (type := payload)
        (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState)), ?_⟩
    exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState post

  | @initialized context nextContext scope mode id node binder initializer initializerNode rest expected type lowered body
      found form member mono extended ordinary initializerFound valueType typed certified allocation annotation same remaining ih =>
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready
      finalContext outcome after trace
    have unique := runtime.graph.nodeOccurrencesUnique
    rcases CallableIndexedOwnedPreparedStagedScopedLexicalSourceInversion.initialized
        (by simpa only [sourceEq] using unique) (by simpa only [sourceEq] using found) form mono
        (by simpa only [sourceEq] using extended) trace with
      ⟨childSize, failure, sameSize, contextEq, outcomeEq, child⟩ |
      ⟨childSize, tailSize, sourceValue, location, middle, bound, sameSize, child, allocated, remainingTrace⟩
    · subst finalContext
      subst outcome
      have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
        rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
          maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
        children context runtime covers sameLedger childSize childStrict certified
          (by simpa only [sourceEq] using initializerFound) (by simpa only [sourceEq] using typed)
          environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation child
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, CellAwareOrdinaryContinuation.failure evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, metadata, effect, reached, related, post.at_fault_type⟩
    · have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
        rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
      have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
        rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
      obtain ⟨value, middleStore, middleMap, middleWorld, evaluated, represented, middleHeaps,
          maps, worlds, frame, metadata, effect, middleState, expressionRelated, post⟩ :=
        children context runtime covers sameLedger childSize childStrict certified
          (by simpa only [sourceEq] using initializerFound) (by simpa only [sourceEq] using typed)
          environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation child
      cases represented with
      | @value _ coreValue payload =>
        let middlePhysical := physical.transport effect frame
        obtain ⟨marker, agreement, _smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
            preserved, allocationEffect, nextAuthority, reached, related, nextAdmitted, nextPhysical, locationEq, nativeEq⟩ :=
          CellAwareNamedOrdinaryPrefix.complete bridge mono member extended ordinary allocation annotation same producer registered
            evaluated (valueType ▸ payload) (valueType ▸ post.at_value.1)
            (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
            middleState post.at_value.2 (authority.transport effect) middlePhysical
            (ready middleState middlePhysical.read) allocated type body
        have nextReady : ProtectedStateTransition.CellAllocation.ReadyAt producer nextPhysical.location nextPhysical.native := by
          intro index current stored
          have previous := ready current (by simpa only [locationEq, nativeEq, middlePhysical, CellAwareScopePhysical.Physical.transport_location, CellAwareScopePhysical.Physical.transport_native] using stored)
          simpa only [locationEq, nativeEq, middlePhysical, CellAwareScopePhysical.Physical.transport_location, CellAwareScopePhysical.Physical.transport_native] using previous
        obtain ⟨value, finalStore, finalMap, finalWorld, tailEvaluated, represented, finalHeaps,
            tailMaps, tailWorlds, finalFrame, finalMetadata, finalEffect, tailState, tailRelated, tailPost⟩ :=
          ih _ tailWithin nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
            (runtime.transport (.ofBinderExtends extended))
            ((Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers)
            ((Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger)
            (ProtectedStateImperativeStatementSuffixTyping.let_decl unique sourceTyped found form extended)
            reached nextAdmitted nextAuthority nextPhysical owner (sameLocation.trans locationEq.symm) nextReady remainingTrace
        let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
          (id := binder.id) (type := lowered.type)
          (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState
        refine ⟨value, finalStore, finalMap, finalWorld, agreement.wrap tailEvaluated, represented, finalHeaps,
          maps.trans (allocationEffect.maps.trans tailMaps), worlds.trans (allocationEffect.worlds.trans tailWorlds),
          frame.trans (preserved.trans finalFrame), metadata.trans (allocationEffect.metadata.trans finalMetadata),
          effect.trans (allocationEffect.trans finalEffect), finalState,
          protocol.trans expressionRelated (protocol.trans related (protocol.trans tailRelated (bindings.restore_related
            (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
            (id := binder.id) (type := lowered.type)
            (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState))), ?_⟩
        exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
          (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState tailPost
  | @nil context scope mode expected type allowed =>
    intro size _within
    exact CellAwareScopeEmptyFlow.preserves bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
      administrative scope mode expected type allowed size
  | @returnUnit context scope mode id node rest found form =>
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready finalContext outcome after trace
    exact CellAwareScopeTerminalFlow.unit_preserves bridge producer unitValue
      (by simpa only [sourceEq] using found) form
      (by simpa only [sourceEq] using runtime.graph.nodeOccurrencesUnique) size
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready trace
  | @returning context scope mode id node expression expressionNode expected lowered rest found form expressionFound valueType typed certified =>
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready finalContext outcome after trace
    have head : CallableIndexedOwnedAdmittedStagedScopedTerminalStatements.Head invocation expression mode (id :: rest) :=
      .returning rest (by simpa only [sourceEq] using lookupStatement?_sound found) form
    have childTyped : ExpressionHasType invocation.source context expression expressionNode.type := by simpa only [sourceEq] using typed
    have meaning := CellAwareScopeTerminalFlow.preserves (administrative := administrative) bridge producer
      (by simpa only [sourceEq] using runtime.graph.nodeOccurrencesUnique)
      head (by simpa only [sourceEq] using expressionFound) childTyped certified budget
      (children context runtime covers sameLedger)
    rw [valueType] at meaning
    exact meaning size within environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready trace
  | @tail context scope id node expression expressionNode expected lowered found form expressionFound valueType typed certified =>
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready finalContext outcome after trace
    have head : CallableIndexedOwnedAdmittedStagedScopedTerminalStatements.Head invocation expression true [id] :=
      .tail (by simpa only [sourceEq] using lookupStatement?_sound found) form
    have childTyped : ExpressionHasType invocation.source context expression expressionNode.type := by simpa only [sourceEq] using typed
    have meaning := CellAwareScopeTerminalFlow.preserves (administrative := administrative) bridge producer
      (by simpa only [sourceEq] using runtime.graph.nodeOccurrencesUnique)
      head (by simpa only [sourceEq] using expressionFound) childTyped certified budget
      (children context runtime covers sameLedger)
    rw [valueType] at meaning
    exact meaning size within environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready trace
  | @discard context scope mode id node expression expressionNode semicolon rest expected lowered type body found form _notTail continuing expressionFound typed certified remaining ih =>
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready finalContext outcome after trace
    exact CellAwareScopeDiscardFlow.preserves bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
      administrative scope mode expected type sourceEq
      (by simpa only [sourceEq] using runtime.graph.nodeOccurrencesUnique)
      (by simpa only [sourceEq] using found) form continuing
      (by simpa only [sourceEq] using expressionFound) (by simpa only [sourceEq] using typed) certified
      budget (children context runtime covers sameLedger) ih size within
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready trace
  | @block context scope mode id node statements rest expected type innerCode body found form inner remaining innerIH remainingIH =>
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready finalContext outcome after trace
    exact CellAwareScopeBlockFlow.preserves bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
      administrative scope mode expected type sourceEq
      (by simpa only [sourceEq] using runtime.graph.nodeOccurrencesUnique)
      (by simpa only [sourceEq] using found) form budget innerIH remainingIH size within
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready trace
  | @ifThen context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body
      found form conditionFound conditionType conditionTyped conditionCertificate thenTree elseTree remaining thenIH elseIH remainingIH =>
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready finalContext outcome after trace
    exact CellAwareScopeConditionalFlow.preserves bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
      administrative scope expected type booleans
      (by simpa only [sourceEq] using conditionFound) conditionType
      (by simpa only [sourceEq] using conditionTyped) conditionCertificate sourceEq
      (by simpa only [sourceEq] using runtime.graph.nodeOccurrencesUnique)
      (by simpa only [sourceEq] using found) form budget (children context runtime covers sameLedger)
      thenIH elseIH remainingIH size within
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready trace
  | @whileLoop context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body escaped
      found form conditionFound conditionType conditionTyped conditionCertificate loopTree nativeTyped remaining loopIH remainingIH =>
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready finalContext outcome after trace
    exact CellAwareLoopSequences.preserves bridge (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) producer transport booleans sourceEq
      (children context runtime covers sameLedger)
      (by simpa only [sourceEq] using conditionFound) conditionType
      (by simpa only [sourceEq] using conditionTyped) conditionCertificate nativeTyped loopIH
      (by simpa only [sourceEq] using runtime.graph.nodeOccurrencesUnique)
      (by simpa only [sourceEq] using found) form remainingIH within
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready trace
  | @forLoop context loopContext postContext scope loopScope postScope mode id node initialItems condition conditionNode postItems statements rest expected type conditionCode loopCode postCode initialCode body escaped
      found form initialTree conditionFound conditionType conditionTyped conditionCertificate loopTree postTree loopSourceTyped postSourceTyped nativeTyped remaining loopIH remainingIH =>
    have postMeaning := CellAwareForPostTreeBounds.preserves (expected := expected) bridge bindings transport functions extension compiled producer registered operandIncluded faithful observations assignmentDiagnostics
      children sourceEq postTree
    have terminalMeaning : CellAwareScopeForInitialBounds.PreservesAtMost bridge loopContext
        (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
        administrative loopScope [] condition postItems statements expected type
        (LocalLoop.iterate type conditionCode loopCode postCode escaped) budget := by
      intro terminalSize within mapping world actualContext environment canonical actual before store embedding
        environments heaps locals agrees actualTyped runtime covers sameLedger initial admitted authority physical owner sameLocation ready outcome after trace
      exact CellAwareForInitialTerminal.preserves bridge (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions)
        producer transport booleans (children loopContext runtime covers sameLedger)
        (by simpa only [sourceEq] using conditionFound) conditionType
        (by simpa only [sourceEq] using conditionTyped) conditionCertificate nativeTyped loopIH postMeaning
        loopSourceTyped postSourceTyped terminalSize within
        environments heaps locals agrees actualTyped runtime covers sameLedger initial admitted authority physical owner sameLocation ready trace
    have initialMeaning := CellAwareForInitialTreeBounds.preserves bridge bindings transport functions extension compiled producer registered operandIncluded faithful observations assignmentDiagnostics
      children sourceEq initialTree terminalMeaning
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready finalContext outcome after trace
    exact CellAwareForSequences.preserves bridge (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) producer sourceEq
      initialMeaning
      (by simpa only [sourceEq] using runtime.graph.nodeOccurrencesUnique)
      (by simpa only [sourceEq] using found) form remainingIH within
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready trace
  | @assign context scope mode id node assignment operator rhs rest expected type body
      found form head bare _rightTyped operands remaining remainingIH =>
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready finalContext outcome after trace
    cases invocation with
    | mk origin actualSource owned stageContext evidence guards =>
      cases sourceEq
      exact CellAwareScopeBareAssignmentFlow.preserves bridge transport functions producer rfl
        runtime.graph.nodeOccurrencesUnique found form head bare extension
        (fun previous right invalid => operandIncluded _ _ (operands previous right invalid))
        budget (children context runtime covers sameLedger) remainingIH size within
        environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
        initial admitted authority physical owner sameLocation ready trace

  | @assignProjected context scope mode id node assignment operator rhs rest expected type body
      found form head projected _rightTyped site remaining remainingIH =>
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready finalContext outcome after trace
    cases invocation with
    | mk origin actualSource owned stageContext evidence guards =>
      cases sourceEq
      exact CellAwareScopeProjectedAssignmentFlow.preserves bridge transport functions producer rfl
        runtime.graph.nodeOccurrencesUnique found form head projected extension faithful observations
        (fun typed _ _ initial => PreparedAssignmentReachedDiagnostics.shape_errors
          (site receiving) operandIncluded assignmentDiagnostics typed initial)
        budget (children context runtime covers sameLedger) remainingIH size within
        environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
        initial admitted authority physical owner sameLocation ready trace

  | @breaking context scope mode id node expected type rest found form =>
    intro size _within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready finalContext outcome after trace
    exact CellAwareScopeTransferFlow.breaking_preserves bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
      administrative scope mode expected type
      (by simpa only [sourceEq] using runtime.graph.nodeOccurrencesUnique)
      (by simpa only [sourceEq] using found) form size
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready trace
  | @continuing context scope mode id node expected type rest found form =>
    intro size _within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready finalContext outcome after trace
    exact CellAwareScopeTransferFlow.continuing_preserves bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
      administrative scope mode expected type
      (by simpa only [sourceEq] using runtime.graph.nodeOccurrencesUnique)
      (by simpa only [sourceEq] using found) form size
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready trace

include record bindings transport extension registered operandIncluded faithful observations assignmentDiagnostics booleans unitValue in
theorem reflects (functionTypes : FunctionRuntimeViews functions) {budget : Nat}
    (children : ∀ context, Dynamic.SourceRuntimeValid program context (source named) →
      invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      CellAwareScopeExpressionBounds.ReflectsBelow bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named registry invocation
      (certificates context) faults budget)
    (sourceEq : invocation.source = source named)
    {administrative : Core.Context} {reasonAt : ExpressionId → Word}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : CellAwareImperativeTree.Tree whole.indexed named compiled certificates administrative reasonAt
      context scope mode statements expected type code)
    (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed named reasonAt) :
    CellAwareScopeFlowBounds.ReflectsAtMost bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
      administrative scope mode statements expected type code budget := by
  induction tree with
  | @generalizedInitialized context nextContext scope mode id node binder initializer initializerNode parameters result lambdaBody
      rest expected type lowered body childFuel found form declaration polymorphic extended ordinary
      initializerFound initializerForm valueType requirements coercions site initialReceipt nativeTyped allocation annotation same captured copied remaining ih =>
    intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready
      completed
    obtain ⟨copies, snapshotHeap, snapshot⟩ := CellAwareGeneralizedSourceInversion.copies_exist (source named) locals
    let function := Dynamic.GeneralizedClosure.ofDirectLambda context (source named) copies binder initializer
      parameters result lambdaBody
    have captures : Dynamic.GeneralizedClosureCaptures context (source named) copies binder initializer function :=
      .directLambda (lookupExpression?_sound initializerFound) initializerForm
        (by simpa only [ExpressionNode.rawType, coercions] using valueType) valueType requirements coercions
    let location : Dynamic.Location := ⟨snapshotHeap.cells.length⟩
    let bound : Dynamic.Heap := ⟨snapshotHeap.cells ++ [⟨function.binder.scheme.body, none, some function⟩]⟩
    have allocated : Dynamic.Heap.AllocatesGeneralized snapshotHeap function location bound := .append
    have unique := runtime.graph.nodeOccurrencesUnique
    obtain ⟨control, next, facts, headTyped⟩ := head_typed sourceTyped
    have functionTyped := CellAwareGeneralizedSourceInversion.captured_wellTyped runtime (snapshot.agrees locals)
      headTyped
      found form polymorphic captures
    obtain ⟨values, marker, copiedStore, copiedMap, copiedWorld, _agreement, smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
        preserved, effect, nextAuthority, reached, related, nextAdmitted, nextPhysical, locationEq, nativeEq⟩ :=
      CellAwareNamedGeneralizedPrefix.complete bridge compiled record site initialReceipt issuer declaration polymorphic extended
        ordinary nativeTyped allocation annotation same copied producer bindings registered environments heaps locals agrees
        actualTyped initial admitted authority physical ready snapshot captures functionTyped allocated type body
    obtain ⟨tailSize, strict, tailCompleted⟩ := smaller completed
    have nextReady : ProtectedStateTransition.CellAllocation.ReadyAt producer nextPhysical.location nextPhysical.native := by
      intro index current stored
      have previous := ready current (by simpa only [locationEq, nativeEq] using stored)
      simpa only [locationEq, nativeEq] using previous
    obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
        maps, worlds, finalFrame, metadata, finalEffect, tailState, tailRelated, post⟩ :=
      ih _ (Nat.le_trans (Nat.le_of_lt strict) within) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
        (runtime.transport (.ofBinderExtends extended))
        ((Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers)
        ((Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger)
        (ProtectedStateImperativeStatementSuffixTyping.let_decl unique sourceTyped found form extended)
        reached nextAdmitted nextAuthority nextPhysical owner (sameLocation.trans locationEq.symm) nextReady tailCompleted
    let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (id := binder.id) (type := lowered.type)
      (value := .cellRef (OptionalCell.cellType lowered.type) (copiedStore.length + 2)) tailState
    refine ⟨Staging.Recursive.Size.stepSize [sourceSize], finalContext, outcome, after, finalMap, finalWorld,
      .letGeneralized (by simpa only [sourceEq] using lookupStatement?_sound found) form
        (by simpa only [sourceEq] using snapshot) (by simpa only [sourceEq] using captures) polymorphic (by simpa only [sourceEq] using extended) allocated trace,
      represented, finalHeaps, effect.maps.trans maps, effect.worlds.trans worlds, preserved.trans finalFrame,
      effect.metadata.trans metadata, effect.trans finalEffect, finalState,
      protocol.trans related (protocol.trans tailRelated (bindings.restore_related
        (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := binder.id) (type := lowered.type)
        (value := .cellRef (OptionalCell.cellType lowered.type) (copiedStore.length + 2)) tailState)), ?_⟩
    exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (copiedStore.length + 2)) tailState post

  | @uninitialized context nextContext scope mode id node binder rest expected type body payload
      found form member mono extended ordinary projected allocation annotation same remaining ih =>
    intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready
      completed
    let location : Dynamic.Location := ⟨before.cells.length⟩
    let bound : Dynamic.Heap := ⟨before.cells ++ [⟨binder.scheme.body, none, none⟩]⟩
    have allocated : Dynamic.Heap.Allocates before binder.scheme.body none location bound := .append
    have unique := runtime.graph.nodeOccurrencesUnique
    obtain ⟨marker, _agreement, smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
        preserved, effect, nextAuthority, reached, related, nextAdmitted, nextPhysical, locationEq, nativeEq⟩ :=
      CellAwareNamedAbsentPrefix.complete bridge mono member extended ordinary allocation annotation same producer registered
        projected environments heaps locals agrees actualTyped initial admitted authority physical
        (ready initial physical.read) allocated body
    obtain ⟨tailSize, strict, tailCompleted⟩ := smaller completed
    have nextReady : ProtectedStateTransition.CellAllocation.ReadyAt producer nextPhysical.location nextPhysical.native := by
      intro index current stored
      have previous := ready current (by simpa only [locationEq, nativeEq] using stored)
      simpa only [locationEq, nativeEq] using previous
    obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
        maps, worlds, finalFrame, metadata, finalEffect, tailState, tailRelated, post⟩ :=
      ih _ (Nat.le_trans (Nat.le_of_lt strict) within) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
        (runtime.transport (.ofBinderExtends extended))
        ((Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers)
        ((Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger)
        (ProtectedStateImperativeStatementSuffixTyping.let_decl unique sourceTyped found form extended)
        reached nextAdmitted nextAuthority nextPhysical owner (sameLocation.trans locationEq.symm) nextReady tailCompleted
    let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (id := binder.id) (type := payload)
      (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState
    refine ⟨Staging.Recursive.Size.stepSize [sourceSize], finalContext, outcome, after, finalMap, finalWorld,
      .letUninitialized (by simpa only [sourceEq] using lookupStatement?_sound found) form
        mono (by simpa only [sourceEq] using extended) allocated trace,
      represented, finalHeaps, effect.maps.trans maps, effect.worlds.trans worlds, preserved.trans finalFrame,
      effect.metadata.trans metadata, effect.trans finalEffect, finalState,
      protocol.trans related (protocol.trans tailRelated (bindings.restore_related
        (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := binder.id) (type := payload)
        (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState)), ?_⟩
    exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState post

  | @initialized context nextContext scope mode id node binder initializer initializerNode rest expected type lowered body
      found form member mono extended ordinary initializerFound valueType typed certified allocation annotation same remaining ih =>
    intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready
      completed
    have original := completed
    rw [TypedLexicalControl.sequence_rename] at original
    obtain ⟨childSize, middleStore, input, childSmaller, childEvaluation⟩ := original.bind_computation
    obtain ⟨childSourceSize, sourceOutcome, middle, middleMap, middleWorld, child, represented, middleHeaps,
        maps, worlds, frame, metadata, effect, middleState, expressionRelated, post⟩ :=
      children context runtime covers sameLedger childSize (Nat.lt_of_lt_of_le childSmaller within) certified
        (by simpa only [sourceEq] using initializerFound) (by simpa only [sourceEq] using typed)
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation childEvaluation
    cases represented with
    | fault matched =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound
        (CellAwareOrdinaryContinuation.failure childEvaluation.sound)
      exact ⟨Staging.Recursive.Size.stepSize [childSourceSize], context, _, middle, middleMap, middleWorld,
        .letFault (by simpa only [sourceEq] using lookupStatement?_sound found) form mono child,
        .fault matched, middleHeaps, maps, worlds, frame, metadata, effect, middleState, expressionRelated, post.at_fault_type⟩
    | @value sourceValue coreValue payload =>
      let location : Dynamic.Location := ⟨middle.cells.length⟩
      let bound : Dynamic.Heap := ⟨middle.cells ++ [⟨binder.scheme.body, some sourceValue, none⟩]⟩
      have allocated : Dynamic.Heap.Allocates middle binder.scheme.body (some sourceValue) location bound := .append
      let middlePhysical := physical.transport effect frame
      obtain ⟨marker, _agreement, smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
          preserved, allocationEffect, nextAuthority, reached, related, nextAdmitted, nextPhysical, locationEq, nativeEq⟩ :=
        CellAwareNamedOrdinaryPrefix.complete bridge mono member extended ordinary allocation annotation same producer registered
          childEvaluation.sound (valueType ▸ payload) (valueType ▸ post.at_value.1)
          (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
          middleState post.at_value.2 (authority.transport effect) middlePhysical
          (ready middleState middlePhysical.read) allocated type body
      obtain ⟨tailSize, tailStrict, tailEvaluation⟩ := smaller completed
      have nextReady : ProtectedStateTransition.CellAllocation.ReadyAt producer nextPhysical.location nextPhysical.native := by
        intro index current stored
        have previous := ready current (by simpa only [locationEq, nativeEq, middlePhysical, CellAwareScopePhysical.Physical.transport_location, CellAwareScopePhysical.Physical.transport_native] using stored)
        simpa only [locationEq, nativeEq, middlePhysical, CellAwareScopePhysical.Physical.transport_location, CellAwareScopePhysical.Physical.transport_native] using previous
      obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
          tailMaps, tailWorlds, finalFrame, finalMetadata, finalEffect, tailState, tailRelated, tailPost⟩ :=
        ih _ (Nat.le_trans (Nat.le_of_lt tailStrict) within) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
          (runtime.transport (.ofBinderExtends extended))
          ((Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers)
          ((Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger)
          (ProtectedStateImperativeStatementSuffixTyping.let_decl runtime.graph.nodeOccurrencesUnique sourceTyped found form extended)
          reached nextAdmitted nextAuthority nextPhysical owner (sameLocation.trans locationEq.symm) nextReady tailEvaluation
      let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := binder.id) (type := lowered.type)
        (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState
      refine ⟨Staging.Recursive.Size.stepSize [childSourceSize, sourceSize], finalContext, outcome, after, finalMap, finalWorld,
        .letInitialized (by simpa only [sourceEq] using lookupStatement?_sound found) form child mono
          (by simpa only [sourceEq] using extended) allocated trace,
        represented, finalHeaps, maps.trans (allocationEffect.maps.trans tailMaps), worlds.trans (allocationEffect.worlds.trans tailWorlds),
        frame.trans (preserved.trans finalFrame), metadata.trans (allocationEffect.metadata.trans finalMetadata),
        effect.trans (allocationEffect.trans finalEffect), finalState,
        protocol.trans expressionRelated (protocol.trans related (protocol.trans tailRelated (bindings.restore_related
          (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
          (id := binder.id) (type := lowered.type)
          (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState))), ?_⟩
      exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState tailPost
  | @nil context scope mode expected type allowed =>
    intro size _within
    exact CellAwareScopeEmptyFlow.reflects bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
      administrative scope mode expected type allowed size
  | @returnUnit context scope mode id node rest found form =>
    intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed
    exact CellAwareScopeTerminalFlow.unit_reflects bridge producer unitValue
      (by simpa only [sourceEq] using found) form size
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed
  | @returning context scope mode id node expression expressionNode expected lowered rest found form expressionFound valueType typed certified =>
    intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed
    have head : CallableIndexedOwnedAdmittedStagedScopedTerminalStatements.Head invocation expression mode (id :: rest) :=
      .returning rest (by simpa only [sourceEq] using lookupStatement?_sound found) form
    have childTyped : ExpressionHasType invocation.source context expression expressionNode.type := by simpa only [sourceEq] using typed
    have meaning := CellAwareScopeTerminalFlow.reflects (administrative := administrative) bridge producer
      head (by simpa only [sourceEq] using expressionFound) childTyped certified budget
      (children context runtime covers sameLedger)
    rw [valueType] at meaning
    exact meaning size within environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed
  | @tail context scope id node expression expressionNode expected lowered found form expressionFound valueType typed certified =>
    intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed
    have head : CallableIndexedOwnedAdmittedStagedScopedTerminalStatements.Head invocation expression true [id] :=
      .tail (by simpa only [sourceEq] using lookupStatement?_sound found) form
    have childTyped : ExpressionHasType invocation.source context expression expressionNode.type := by simpa only [sourceEq] using typed
    have meaning := CellAwareScopeTerminalFlow.reflects (administrative := administrative) bridge producer
      head (by simpa only [sourceEq] using expressionFound) childTyped certified budget
      (children context runtime covers sameLedger)
    rw [valueType] at meaning
    exact meaning size within environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed
  | @discard context scope mode id node expression expressionNode semicolon rest expected lowered type body found form _notTail continuing expressionFound typed certified remaining ih =>
    intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed
    exact CellAwareScopeDiscardFlow.reflects bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
      administrative scope mode expected type sourceEq
      (by simpa only [sourceEq] using runtime.graph.nodeOccurrencesUnique)
      (by simpa only [sourceEq] using found) form continuing
      (by simpa only [sourceEq] using expressionFound) (by simpa only [sourceEq] using typed) certified
      budget (children context runtime covers sameLedger) ih size within
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed
  | @block context scope mode id node statements rest expected type innerCode body found form inner remaining innerIH remainingIH =>
    intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed
    exact CellAwareScopeBlockFlow.reflects bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
      administrative scope mode expected type sourceEq
      (by simpa only [sourceEq] using runtime.graph.nodeOccurrencesUnique)
      (by simpa only [sourceEq] using found) form budget innerIH remainingIH size within
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed
  | @ifThen context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body
      found form conditionFound conditionType conditionTyped conditionCertificate thenTree elseTree remaining thenIH elseIH remainingIH =>
    intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed
    exact CellAwareScopeConditionalFlow.reflects bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
      administrative scope expected type booleans
      (by simpa only [sourceEq] using conditionFound) conditionType
      (by simpa only [sourceEq] using conditionTyped) conditionCertificate sourceEq
      (by simpa only [sourceEq] using runtime.graph.nodeOccurrencesUnique)
      (by simpa only [sourceEq] using found) form budget (children context runtime covers sameLedger)
      thenIH elseIH remainingIH size within
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed

  | @whileLoop context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body escaped
      found form conditionFound conditionType conditionTyped conditionCertificate loopTree nativeTyped remaining loopIH remainingIH =>
    intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed
    exact CellAwareLoopSequences.reflects bridge (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) producer transport booleans sourceEq
      (children context runtime covers sameLedger)
      (by simpa only [sourceEq] using conditionFound) conditionType
      (by simpa only [sourceEq] using conditionTyped) conditionCertificate nativeTyped loopIH
      (by simpa only [sourceEq] using found) form remainingIH within
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed
  | @forLoop context loopContext postContext scope loopScope postScope mode id node initialItems condition conditionNode postItems statements rest expected type conditionCode loopCode postCode initialCode body escaped
      found form initialTree conditionFound conditionType conditionTyped conditionCertificate loopTree postTree loopSourceTyped postSourceTyped nativeTyped remaining loopIH remainingIH =>
    have postMeaning := CellAwareForPostTreeBounds.reflects (expected := expected) bridge bindings transport functions extension compiled producer registered operandIncluded faithful observations assignmentDiagnostics functionTypes
      children sourceEq postTree
    have terminalMeaning : CellAwareScopeForInitialBounds.ReflectsAtMost bridge loopContext
        (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
        administrative loopScope [] condition postItems statements expected type
        (LocalLoop.iterate type conditionCode loopCode postCode escaped) budget := by
      intro terminalSize within mapping world actualContext environment canonical actual before store embedding value finalStore
        environments heaps locals agrees actualTyped runtime covers sameLedger initial admitted authority physical owner sameLocation ready completed
      exact CellAwareForInitialTerminal.reflects bridge (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions)
        producer transport booleans (children loopContext runtime covers sameLedger)
        (by simpa only [sourceEq] using conditionFound) conditionType
        (by simpa only [sourceEq] using conditionTyped) conditionCertificate nativeTyped loopIH postMeaning
        loopSourceTyped postSourceTyped terminalSize within
        environments heaps locals agrees actualTyped runtime covers sameLedger initial admitted authority physical owner sameLocation ready completed
    have initialMeaning := CellAwareForInitialTreeBounds.reflects bridge bindings transport functions extension compiled producer registered operandIncluded faithful observations assignmentDiagnostics functionTypes
      children sourceEq initialTree terminalMeaning
    intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed
    exact CellAwareForSequences.reflects bridge (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) producer sourceEq
      initialMeaning
      (by simpa only [sourceEq] using found) form remainingIH within
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed
  | @assign context scope mode id node assignment operator rhs rest expected type body
      found form head bare _rightTyped operands remaining remainingIH =>
    intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed
    cases invocation with
    | mk origin actualSource owned stageContext evidence guards =>
      cases sourceEq
      exact CellAwareScopeBareAssignmentFlow.reflects bridge transport functions producer rfl
        runtime.graph.nodeOccurrencesUnique found form head bare extension
        (fun previous right invalid => operandIncluded _ _ (operands previous right invalid))
        budget (children context runtime covers sameLedger) remainingIH size within
        environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
        initial admitted authority physical owner sameLocation ready completed

  | @assignProjected context scope mode id node assignment operator rhs rest expected type body
      found form head projected _rightTyped site remaining remainingIH =>
    intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed
    cases invocation with
    | mk origin actualSource owned stageContext evidence guards =>
      cases sourceEq
      exact CellAwareScopeProjectedAssignmentFlow.reflects bridge transport functions producer rfl
        runtime.graph.nodeOccurrencesUnique found form head projected extension faithful observations
        (fun typed _ _ initial => PreparedAssignmentReachedDiagnostics.shape_errors
          (site receiving) operandIncluded assignmentDiagnostics typed initial)
        functionTypes budget (children context runtime covers sameLedger) remainingIH size within
        environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
        initial admitted authority physical owner sameLocation ready completed

  | @breaking context scope mode id node expected type rest found form =>
    intro size _within mapping world actualContext environment canonical actual before store embedding value finalStore
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed
    exact CellAwareScopeTransferFlow.breaking_reflects bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
      administrative scope mode expected type
      (by simpa only [sourceEq] using found) form size
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed
  | @continuing context scope mode id node expected type rest found form =>
    intro size _within mapping world actualContext environment canonical actual before store embedding value finalStore
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed
    exact CellAwareScopeTransferFlow.continuing_reflects bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
      administrative scope mode expected type
      (by simpa only [sourceEq] using found) form size
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed

end Solcore.SourceSemantics.CoreLowering.CellAwareImperativeTreeBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareImperativeSourceTreeLifting
/-! Independent ordinary Source bodies follow the actual compiler tree.
Generalized declarations construct their real physical state before recursion. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CellAwareImperativeSourceTreeLifting
open Core Frontend SourceInference CompatibleEquality GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (bindings : ProtectedStateTransition.Bindings protocol)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  (functions : FunctionModel whole.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions whole.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial whole.compatible.checked).registry receiving)
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  (compiled : CallableIndexedNamedGeneration.Compilation whole.indexed named diagnostics namedCode)
  (record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan named.signature.key = .ok named.specialized)
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) (GeneralizedLocalInstanceValues.model whole.indexed)))
  {faults : RecursiveStageMeaning.FaultRep}
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
  (operandIncluded : ∀ reason token,
    GenericAssignmentDiagnostics.OperandRep compiled.own.assignments reason token → faults (.semantic reason) token)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations whole.compatible.checked.catalog functions identities)
  (assignmentDiagnostics : PreparedAssignmentReachedDiagnostics.Ready (values := .initial whole.compatible.checked)
    functions protocol (source named)
    (fun site root => diagnostics.placeReason named.signature.key site root none)
    (fun site root raw => diagnostics.placeReason named.signature.key site root (some raw))
    receiving (fun reason token => faults (.semantic reason) token))
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}


variable
  (booleans : ∀ {mapping world sourceValue nativeValue},
    (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions).Represents mapping world .bool sourceValue nativeValue .bool →
    ∃ truth, sourceValue = .bool truth ∧ nativeValue = .bool truth)
  (unitValue : ∀ mapping world, (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions).Represents mapping world .unit .unit .unit .unit)

include record registered bindings transport extension operandIncluded faithful observations assignmentDiagnostics booleans unitValue in
theorem lifts
    (children : ∀ context, Dynamic.SourceRuntimeValid program context (source named) →
      invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeSourceLiftBounds.LiftsAt bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named registry invocation (certificates context) size)
    (preservation : ∀ context, Dynamic.SourceRuntimeValid program context (source named) →
      invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeExpressionBounds.PreservesAt bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named registry invocation
        (certificates context) faults size)
    (sourceEq : invocation.source = source named)
    {administrative : Core.Context} {reasonAt : ExpressionId → Word}
    {mode : Bool} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : CellAwareImperativeTree.Tree whole.indexed named compiled certificates administrative reasonAt
      context scope mode statements expected type code)
    (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed named reasonAt) :
    CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope mode statements := by
  induction tree with
  | @generalizedInitialized context nextContext scope mode id node binder initializer initializerNode parameters result lambdaBody rest expected type lowered body childFuel
      found form declaration polymorphic extended ordinary initializerFound initializerForm valueType requirements coercions site initial nativeTyped allocation annotation same captured copied remaining ih =>
    exact CellAwareSourceFlowGeneralizedLifting.generalized bridge bindings compiled record producer registered
      (type := type) (body := body) found form declaration polymorphic extended ordinary initializerFound initializerForm
      valueType requirements coercions site initial nativeTyped allocation annotation same copied sourceEq issuer ih
  | @initialized context nextContext scope mode id node binder initializer initializerNode rest expected type lowered body
      found form member mono extended ordinary initializerFound valueType typed certified allocation annotation same remaining ih =>
    exact CellAwareSourceFlowOrdinaryLifting.initialized bridge producer registered (type := type) (body := body)
      found form member mono extended ordinary initializerFound valueType typed certified allocation annotation same
      sourceEq (children _) (preservation _) ih

  | @uninitialized context nextContext scope mode id node binder rest expected type body payload
      found form member mono extended ordinary projected allocation annotation same remaining ih =>
    exact CellAwareSourceFlowAbsentLifting.absent bridge producer registered (body := body)
      found form member mono extended ordinary projected allocation annotation same sourceEq ih

  | nil _allowed => exact CellAwareSourceFlowTerminalLifting.nil bridge producer
  | returnUnit rest found form =>
    exact CellAwareSourceFlowTerminalLifting.return_unit bridge producer sourceEq
      (by simpa only [sourceEq] using found) form
  | @returning context scope mode id node expression expressionNode expected lowered rest found form expressionFound _valueType typed certified =>
    exact CellAwareSourceFlowTerminalLifting.terminal bridge producer sourceEq
      (.returning rest (by simpa only [sourceEq] using lookupStatement?_sound found) form)
      (by simpa only [sourceEq] using expressionFound) (by simpa only [sourceEq] using typed)
      certified (children context)
  | @tail context scope id node expression expressionNode expected lowered found form expressionFound _valueType typed certified =>
    exact CellAwareSourceFlowTerminalLifting.terminal bridge producer sourceEq
      (.tail (by simpa only [sourceEq] using lookupStatement?_sound found) form)
      (by simpa only [sourceEq] using expressionFound) (by simpa only [sourceEq] using typed)
      certified (children context)
  | @discard context scope mode id node expression expressionNode semicolon rest expected lowered type body
      found form _notTail continuing expressionFound typed certified remaining ih =>
    exact CellAwareSourceFlowDiscardLifting.lifts bridge producer sourceEq
      (by simpa only [sourceEq] using found) form continuing
      (by simpa only [sourceEq] using expressionFound) (by simpa only [sourceEq] using typed)
      certified (children context) (preservation context) ih
  | @block context scope mode id node statements rest expected type innerCode body
      found form inner remaining innerIH remainingIH =>
    exact CellAwareSourceFlowBlockLifting.lifts bridge producer sourceEq
      (by simpa only [sourceEq] using found) form innerIH
      (fun size => CellAwareImperativeTreeBounds.preserves bridge bindings transport functions extension compiled record producer registered operandIncluded faithful observations assignmentDiagnostics
        booleans unitValue (fun context runtime covers sameLedger childSize _ =>
          preservation context runtime covers sameLedger childSize) sourceEq inner issuer size (Nat.le_refl _)) remainingIH
  | @ifThen context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body
      found form conditionFound conditionType conditionTyped conditionCertificate thenTree elseTree remaining thenIH elseIH remainingIH =>
    exact CellAwareSourceFlowConditionalLifting.lifts
      (expected := expected) (type := type) (branchCode := fun truth => if truth then thenCode else elseCode)
      bridge producer sourceEq booleans
      (by simpa only [sourceEq] using found) form
      (by simpa only [sourceEq] using conditionFound) conditionType
      (by simpa only [sourceEq] using conditionTyped) conditionCertificate
      (children context) (preservation context)
      (fun truth => by cases truth <;> assumption)
      (fun truth size => by
        cases truth
        · exact CellAwareImperativeTreeBounds.preserves bridge bindings transport functions extension compiled record producer registered operandIncluded faithful observations assignmentDiagnostics
            booleans unitValue (fun context runtime covers sameLedger childSize _ =>
              preservation context runtime covers sameLedger childSize) sourceEq elseTree issuer size (Nat.le_refl _)
        · exact CellAwareImperativeTreeBounds.preserves bridge bindings transport functions extension compiled record producer registered operandIncluded faithful observations assignmentDiagnostics
            booleans unitValue (fun context runtime covers sameLedger childSize _ =>
              preservation context runtime covers sameLedger childSize) sourceEq thenTree issuer size (Nat.le_refl _)) remainingIH

  | @whileLoop context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body escaped
      found form conditionFound conditionType conditionTyped conditionCertificate loopTree nativeTyped remaining loopIH remainingIH =>
    exact CellAwareSourceWhileSequenceLifting.lifts bridge producer transport sourceEq booleans
      (by simpa only [sourceEq] using found) form
      (by simpa only [sourceEq] using conditionFound) conditionType
      (by simpa only [sourceEq] using conditionTyped) conditionCertificate nativeTyped
      (children context) (preservation context) loopIH
      (fun size => CellAwareImperativeTreeBounds.preserves bridge bindings transport functions extension compiled record producer registered operandIncluded faithful observations assignmentDiagnostics
        booleans unitValue (fun context runtime covers sameLedger childSize _ =>
          preservation context runtime covers sameLedger childSize) sourceEq loopTree issuer size (Nat.le_refl _)) remainingIH
  | @forLoop context loopContext postContext scope loopScope postScope mode id node initialItems condition conditionNode postItems statements rest expected type conditionCode loopCode postCode initialCode body escaped
      found form initialTree conditionFound conditionType conditionTyped conditionCertificate loopTree postTree loopSourceTyped postSourceTyped nativeTyped remaining loopIH remainingIH =>
    have loopMeaning : ∀ size, CellAwareScopeFlowBounds.PreservesAt bridge loopContext
        (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
        administrative loopScope false statements expected type loopCode size :=
      fun size => CellAwareImperativeTreeBounds.preserves bridge bindings transport functions extension compiled record producer registered operandIncluded faithful observations assignmentDiagnostics
        booleans unitValue (fun context runtime covers sameLedger childSize _ =>
          preservation context runtime covers sameLedger childSize) sourceEq loopTree issuer size (Nat.le_refl _)
    have postMeaning : ∀ size, CellAwareScopeForPostBounds.PreservesAt bridge loopContext
        (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
        administrative loopScope postItems expected type postCode size :=
      fun size => CellAwareForPostTreeBounds.preserves bridge bindings transport functions extension compiled producer registered operandIncluded faithful observations assignmentDiagnostics
        (fun context runtime covers sameLedger childSize _ => preservation context runtime covers sameLedger childSize)
        sourceEq postTree size (Nat.le_refl _)
    have terminalMeaning : ∀ size, CellAwareScopeForInitialBounds.PreservesAt bridge loopContext
        (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
        administrative loopScope [] condition postItems statements expected type
        (LocalLoop.iterate type conditionCode loopCode postCode escaped) size := by
      intro terminalSize mapping world actualContext environment canonical actual before store embedding
        environments heaps locals agrees actualTyped runtime covers sameLedger initial admitted authority physical owner sameLocation ready outcome after trace
      exact CellAwareForInitialTerminal.preserves bridge (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions)
        producer transport booleans (fun n _ => preservation loopContext runtime covers sameLedger n)
        (by simpa only [sourceEq] using conditionFound) conditionType
        (by simpa only [sourceEq] using conditionTyped) conditionCertificate nativeTyped
        (fun n _ => loopMeaning n) (fun n _ => postMeaning n)
        loopSourceTyped postSourceTyped terminalSize (Nat.le_refl _)
        environments heaps locals agrees actualTyped runtime covers sameLedger initial admitted authority physical owner sameLocation ready trace
    have initialMeaning : ∀ size, CellAwareScopeForInitialBounds.PreservesAt bridge context
        (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
        administrative scope initialItems condition postItems statements expected type initialCode size :=
      fun size => CellAwareForInitialTreeBounds.preserves bridge bindings transport functions extension compiled producer registered operandIncluded faithful observations assignmentDiagnostics
        (fun context runtime covers sameLedger childSize _ => preservation context runtime covers sameLedger childSize)
        sourceEq initialTree (fun n _ => terminalMeaning n) size (Nat.le_refl _)
    have postLift : CellAwareSourceForLiftBounds.ItemsLifts (named := named) (administrative := administrative)
        (context := loopContext) (scope := loopScope) (registry := registry) (invocation := invocation) bridge producer postItems := CellAwareSourceForHeaderLifting.lifts bridge transport functions faithful observations extension compiled producer registered
      children preservation sourceEq postTree
    have terminalLift : CellAwareSourceForInitialBounds.InitializersLifts (named := named) (administrative := administrative)
        (context := loopContext) (scope := loopScope) (registry := registry) (invocation := invocation) bridge producer [] condition postItems statements := CellAwareSourceForInitialTerminal.lifts bridge producer
      (children loopContext) (preservation loopContext) booleans
      (by simpa only [sourceEq] using conditionFound) conditionType
      (by simpa only [sourceEq] using conditionTyped) conditionCertificate loopIH loopMeaning loopSourceTyped
      postLift postMeaning postSourceTyped
    have initialLift : CellAwareSourceForInitialBounds.InitializersLifts (named := named) (administrative := administrative)
        (context := context) (scope := scope) (registry := registry) (invocation := invocation) bridge producer initialItems condition postItems statements := CellAwareSourceForInitialTreeLifting.lifts bridge transport functions faithful observations extension compiled producer registered
      children preservation sourceEq initialTree terminalLift
    intro size mapping world actualContext environment canonical actual before store embedding
    exact CellAwareSourceForSequenceLifting.lifts bridge producer sourceEq initialLift initialMeaning
      (by simpa only [sourceEq] using found) form remainingIH
  | @assign context scope mode id node assignment operator rhs rest expected type body
      found form head bare _rightTyped _operands remaining remainingIH =>
    cases invocation with
    | mk origin actualSource owned stageContext evidence guards =>
      cases sourceEq
      exact CellAwareSourceFlowAssignmentLifting.lifts bridge functions transport extension producer rfl
        found form head bare (children context) (preservation context) remainingIH

  | @assignProjected context scope mode id node assignment operator rhs rest expected type body
      found form head projected _rightTyped _site remaining remainingIH =>
    cases invocation with
    | mk origin actualSource owned stageContext evidence guards =>
      cases sourceEq
      exact CellAwareSourceFlowProjectedAssignmentLifting.lifts bridge functions faithful observations transport extension producer rfl
        found form head projected (children context) (preservation context) remainingIH

  | breaking rest found form =>
    exact CellAwareSourceTransferLifting.breaking bridge producer sourceEq
      (by simpa only [sourceEq] using found) form
  | continuing rest found form =>
    exact CellAwareSourceTransferLifting.continuing bridge producer sourceEq
      (by simpa only [sourceEq] using found) form

end Solcore.SourceSemantics.CoreLowering.CellAwareImperativeSourceTreeLifting
end
