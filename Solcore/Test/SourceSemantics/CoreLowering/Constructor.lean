import Solcore.Test.SourceSemantics.CoreLowering.OperatorCalls
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicInputRegistries
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalNamedCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.Bootstrap
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.CallRejection
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.SelectedGeneralCalls
import Solcore.SourceSemantics.SourceProgramCheckingSoundness
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.PhysicalPublic
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.LambdaBodySupport
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicPhysicalSessions
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.ProgramAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedCanonicalSupport
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicActualRegistry
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.InitializedPublicBounds
import Solcore.SourceSemantics.CoreLowering.PublicSessionOutcomes
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.PublicDirectSessions
import Solcore.SourceSemantics.CoreLowering.PublicSessions
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicNestedInputs
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionConstructors

/-!
# Constructor call tests

The original constructor operations through one checked compiler profile and public execution.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreConstructorCallsSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreConstructorCalls
open Solcore Frontend SourceInference SourceSemantics
structure FactoryShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  binder : TypedBinder
  read : ExpressionNode
  innerReturn : StatementNode
  expression : ExpressionNode
  statement : StatementNode
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [.function .unit .word]
  inputs : function.typedBody.inputs = [binder]
  binderRequirements : binder.schemeRequirements = []
  roots : function.typedBody.roots = [.statement statement.id]
  readFound : function.typedBody.lookupExpression? read.id = some read
  innerReturnFound : function.typedBody.lookupStatement? innerReturn.id = some innerReturn
  expressionFound : function.typedBody.lookupExpression? expression.id = some expression
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  readForm : read.form = .reference binder.name (.local binder.id)
  readRaw : read.rawType = .word
  readType : read.type = .word
  readRequirements : read.requirements = []
  readCoercions : read.coercions = []
  innerReturnForm : innerReturn.form = .returnStmt (some read.id)
  innerReturnType : innerReturn.type = .word
  lambda : expression.form = .lambda [] .word [innerReturn.id]
  expressionRaw : expression.rawType = .function .unit .word
  expressionType : expression.type = .function .unit .word
  requirements : expression.requirements = []
  coercions : expression.coercions = []
  returnStatement : statement.form = .returnStmt (some expression.id)
  statementType : statement.type = .function .unit .word

private theorem statementRoots_injective {left right : List StatementId}
    (equal : left.map NodeId.statement = right.map NodeId.statement) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp at equal ⊢
  | cons head rest ih =>
    cases right with
    | nil => simp at equal
    | cons other tail =>
      simp only [List.map_cons, List.cons.injEq] at equal
      obtain ⟨same, tails⟩ := equal
      cases same
      simp only [ih tails]

theorem FactoryShape.statementTyping
    {function : CheckedFunction} {signature : ProgramFunctionSignature}
    (shape : FactoryShape function signature) (signatures : ProgramSignatures) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.statement.id] :=
    statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {
    type := .function .unit .word
    hasValue := true
    sawReturn := true
    control := .returned }
  refine ⟨BodyFacts.singleton facts, rfl, ?_⟩
  intro lexical extension
  rw [shape.inputs, shape.inputTypes] at extension
  cases extension with
  | cons scheme head tail =>
    cases tail
    have binders : TypeParameterBindersWellFormed lexical := by
      rw [TypeParameterBindersWellFormed, head.context_fields.2.2.1]
      simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
        Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables,
        shape.parameters]
    have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
    have callable : TypeAdmissible lexical (.function .unit .word) :=
      ⟨binders, .function (.builtin .unit) (.builtin .word)⟩
    have instantiation : LocalSchemeInstantiationValid lexical shape.binder .word [] := by
      refine .intro (LocalSchemeRequirementsWellFormed.empty _ _ shape.binderRequirements)
        (scheme.symm ▸ SchemeWellFormed.monoAdmissible word) [] ?_ ?_ ?_ (by simp) ?_ ?_
      · simpa only [scheme, TypeSystem.Scheme.mono] using ExactSubstitution.empty
      · intro metavariable replacement member; cases member
      · simpa only [scheme, TypeSystem.Scheme.mono] using SchemeInstantiates.empty_apply .word
      · intro id member; cases member
      · rw [instantiateLocalSchemePredicates, shape.binderRequirements]
        exact .nil
    have readTyped : ExpressionHasType function.typedBody lexical shape.read.id .word := by
      rw [← shape.readType]
      refine .intro (lookupExpression?_sound shape.readFound)
        (shape.readForm ▸ ExpressionFormHasRawType.reference
          (.local head.local_self head.local_scheme_requirements_self instantiation))
        shape.readRaw word (shape.readType ▸ word) ?_
      · rw [shape.readRequirements, shape.readCoercions, shape.readType]
        exact .ordinary (by intro id member; cases member) (.nil _) rfl
    have expressionTyped : ExpressionHasType function.typedBody lexical shape.expression.id
        (.function .unit .word) := by
      rw [← shape.expressionType]
      refine .intro (lookupExpression?_sound shape.expressionFound)
        (shape.lambda ▸ ExpressionFormHasRawType.lambda (by simp) (.nil _)
          (.singleton (.returnValue (lookupStatement?_sound shape.innerReturnFound)
            shape.innerReturnForm readTyped shape.innerReturnType))
          (by exact ⟨rfl, rfl, .inl ⟨rfl, rfl⟩⟩)) shape.expressionRaw
        callable (shape.expressionType ▸ callable) ?_
      rw [shape.requirements, shape.coercions, shape.expressionType]
      exact .ordinary (by intro id member; cases member) (.nil _) rfl
    exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.statementFound)
      shape.returnStatement expressionTyped shape.statementType)⟩

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  externalLibraries := []
  mainSources := [{path := "main.solc", content :=
    "enum Holder { Hold(function() returns (Word), function() returns (Word), function(Word) returns (function() returns (Word)), function(integer) returns (Word)) } function make(seed: Word) returns (function() returns (Word)) { return lam() { return seed; }; } function pack(factory: function(Word) returns (function() returns (Word)), next: Word, prior: function() returns (Word), convert: function(integer) returns (Word)) returns (Holder) { return .Hold(factory(next), prior, factory, convert); }"}] }

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

def shape (function : CheckedFunction) (signature : ProgramFunctionSignature) :
    IO (FactoryShape function signature) := do
  let [binder] := function.typedBody.inputs
    | throw (IO.userError "captured factory input shape")
  let [Node.expression read, Node.statement innerReturn,
      Node.expression expression, Node.statement statement] := function.typedBody.nodes
    | throw (IO.userError "captured factory occurrence shape")
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "captured factory parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "captured factory inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.function .unit .word]) "captured factory returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [binder]) "captured factory inputs"
  let ⟨binderRequirements⟩ ← observed (binder.schemeRequirements = []) "captured factory binderRequirements"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "captured factory roots"
  let ⟨readFound⟩ ← observed (function.typedBody.lookupExpression? read.id = some read) "captured factory readFound"
  let ⟨innerReturnFound⟩ ← observed (function.typedBody.lookupStatement? innerReturn.id = some innerReturn) "captured factory innerReturnFound"
  let ⟨expressionFound⟩ ← observed (function.typedBody.lookupExpression? expression.id = some expression) "captured factory expressionFound"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "captured factory statementFound"
  let ⟨readForm⟩ ← observed (read.form = .reference binder.name (.local binder.id)) "captured factory readForm"
  let ⟨readRaw⟩ ← observed (read.rawType = .word) "captured factory readRaw"
  let ⟨readType⟩ ← observed (read.type = .word) "captured factory readType"
  let ⟨readRequirements⟩ ← observed (read.requirements = []) "captured factory readRequirements"
  let ⟨readCoercions⟩ ← observed (read.coercions = []) "captured factory readCoercions"
  let ⟨innerReturnForm⟩ ← observed (innerReturn.form = .returnStmt (some read.id)) "captured factory innerReturnForm"
  let ⟨innerReturnType⟩ ← observed (innerReturn.type = .word) "captured factory innerReturnType"
  let ⟨lambda⟩ ← observed (expression.form = .lambda [] .word [innerReturn.id]) "captured factory lambda"
  let ⟨expressionRaw⟩ ← observed (expression.rawType = .function .unit .word) "captured factory expressionRaw"
  let ⟨expressionType⟩ ← observed (expression.type = .function .unit .word) "captured factory expressionType"
  let ⟨requirements⟩ ← observed (expression.requirements = []) "captured factory requirements"
  let ⟨coercions⟩ ← observed (expression.coercions = []) "captured factory coercions"
  let ⟨returnStatement⟩ ← observed (statement.form = .returnStmt (some expression.id)) "captured factory returnStatement"
  let ⟨statementType⟩ ← observed (statement.type = .function .unit .word) "captured factory statementType"
  return { binder, read, innerReturn, expression, statement, parameters, inputTypes, returns, inputs, binderRequirements, roots, readFound, innerReturnFound, expressionFound, statementFound, readForm, readRaw, readType, readRequirements, readCoercions, innerReturnForm, innerReturnType, lambda, expressionRaw, expressionType, requirements, coercions, returnStatement, statementType }



abbrev Read := Tests.SourceCoreNamedBranch.Read
abbrev TypedNode := Tests.SourceCoreOperatorCalls.TypedNode
abbrev closureType : TypeSystem.Ty := .function .unit .word
abbrev makerType : TypeSystem.Ty := .function .word closureType
abbrev convertType : TypeSystem.Ty := .function .integer .word
abbrev payloadTypes : List TypeSystem.Ty := [closureType, closureType, makerType, convertType]
abbrev containerType (dataType : ProgramDataSignature) : TypeSystem.Ty := .nominal dataType.id []

structure ReadShape (function : CheckedFunction) (signature : ProgramFunctionSignature)
    (dataType : ProgramDataSignature) where
  factory : TypedBinder
  argument : TypedBinder
  prior : TypedBinder
  convert : TypedBinder
  argumentRead : Read function.typedBody argument .word
  factoryRead : Read function.typedBody factory makerType
  call : TypedNode function.typedBody closureType
  application : IndirectCallResolution
  callForm : call.node.form = .call factoryRead.node.id [argumentRead.node.id] (.indirect application)
  applicationEq : application = ⟨1, .word, .word, []⟩
  priorRead : Read function.typedBody prior closureType
  retainedFactoryRead : Read function.typedBody factory makerType
  convertRead : Read function.typedBody convert convertType
  expression : TypedNode function.typedBody (containerType dataType)
  constructor : ProgramDataConstructorSignature
  constructorMember : constructor ∈ dataType.constructors
  constructorOwner : constructor.id.dataType = dataType.id
  constructorPayload : constructor.payloadTypes = payloadTypes
  dataParameters : dataType.parameters = []
  instantiation : DataConstructorInstantiation
  instantiationEq : instantiation = ⟨constructor.id, [], payloadTypes, containerType dataType⟩
  expressionForm : expression.node.form = .constructor instantiation
    [call.node.id, priorRead.node.id, retainedFactoryRead.node.id, convertRead.node.id]
  statement : StatementNode
  factoryScheme : factory.scheme = .mono makerType
  factoryRequirements : factory.schemeRequirements = []
  factoryOrdinary : factory.comptime = false
  argumentScheme : argument.scheme = .mono .word
  argumentRequirements : argument.schemeRequirements = []
  argumentOrdinary : argument.comptime = false
  priorScheme : prior.scheme = .mono closureType
  priorRequirements : prior.schemeRequirements = []
  priorOrdinary : prior.comptime = false
  convertScheme : convert.scheme = .mono convertType
  convertRequirements : convert.schemeRequirements = []
  convertOrdinary : convert.comptime = false
  argumentFactory : argument.id ≠ factory.id
  priorFactory : prior.id ≠ factory.id
  priorArgument : prior.id ≠ argument.id
  convertFactory : convert.id ≠ factory.id
  convertArgument : convert.id ≠ argument.id
  convertPrior : convert.id ≠ prior.id
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [makerType, .word, closureType, convertType]
  returns : signature.returnTypes = [containerType dataType]
  inputs : function.typedBody.inputs = [factory, argument, prior, convert]
  roots : function.typedBody.roots = [.statement statement.id]
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some expression.node.id)
  statementType : statement.type = containerType dataType

def ReadShape.nodeList {function signature dataType} (shape : ReadShape function signature dataType) : List Node :=
  [.expression shape.argumentRead.node, .expression shape.factoryRead.node, .expression shape.call.node,
   .expression shape.priorRead.node, .expression shape.retainedFactoryRead.node, .expression shape.convertRead.node,
   .expression shape.expression.node, .statement shape.statement]

theorem ReadShape.statementTyping {function signature dataType}
    (shape : ReadShape function signature dataType) (signatures : ProgramSignatures)
    (cataloged : dataType ∈ signatures.dataTypes) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.statement.id] := statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type := containerType dataType, hasValue := true, sawReturn := true, control := .returned}
  refine ⟨BodyFacts.singleton facts, rfl, ?_⟩
  intro lexical extension
  rw [shape.inputs, shape.inputTypes] at extension
  cases extension with
  | cons factoryScheme factoryExtended tail =>
    cases tail with
    | cons argumentScheme argumentExtended tail =>
      cases tail with
      | cons priorScheme priorExtended tail =>
        cases tail with
        | cons convertScheme convertExtended tail =>
          cases tail
          have binders : TypeParameterBindersWellFormed lexical := by
            rw [TypeParameterBindersWellFormed, convertExtended.context_fields.2.2.1,
              priorExtended.context_fields.2.2.1, argumentExtended.context_fields.2.2.1,
              factoryExtended.context_fields.2.2.1]
            simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
              Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
          have sameSignatures : lexical.signatures = signatures := by
            rw [convertExtended.context_fields.1, priorExtended.context_fields.1,
              argumentExtended.context_fields.1, factoryExtended.context_fields.1]
            rfl
          have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
          have closure : TypeAdmissible lexical closureType := ⟨binders, .function (.builtin .unit) (.builtin .word)⟩
          have maker : TypeAdmissible lexical makerType := ⟨binders, .function (.builtin .word) closure.2⟩
          have converter : TypeAdmissible lexical convertType := ⟨binders, .function (.builtin .integer) (.builtin .word)⟩
          have dataMember : dataType ∈ lexical.signatures.dataTypes := by rw [sameSignatures]; exact cataloged
          have container : TypeAdmissible lexical (containerType dataType) :=
            ⟨binders, .nominal dataType [] dataMember (by simp [shape.dataParameters]) .nil⟩
          have factoryRead := fun (read : Read function.typedBody shape.factory makerType) =>
            read.typed factoryScheme shape.factoryRequirements maker
              (by cases convertExtended; cases priorExtended; cases argumentExtended
                  exact .tail shape.convertFactory (.tail shape.priorFactory (.tail shape.argumentFactory factoryExtended.local_self)))
              (by cases convertExtended; cases priorExtended; cases argumentExtended
                  exact .tail shape.convertFactory (.tail shape.priorFactory (.tail shape.argumentFactory factoryExtended.local_scheme_requirements_self)))
          have argumentRead := shape.argumentRead.typed argumentScheme shape.argumentRequirements word
            (by cases convertExtended; cases priorExtended
                exact .tail shape.convertArgument (.tail shape.priorArgument argumentExtended.local_self))
            (by cases convertExtended; cases priorExtended
                exact .tail shape.convertArgument (.tail shape.priorArgument argumentExtended.local_scheme_requirements_self))
          have priorRead := shape.priorRead.typed priorScheme shape.priorRequirements closure
            (by cases convertExtended; exact .tail shape.convertPrior priorExtended.local_self)
            (by cases convertExtended; exact .tail shape.convertPrior priorExtended.local_scheme_requirements_self)
          have convertRead := shape.convertRead.typed convertScheme shape.convertRequirements converter
            convertExtended.local_self convertExtended.local_scheme_requirements_self
          have application : IndirectApplicationValid lexical shape.application [.word] .word := by
            rw [shape.applicationEq]; exact .intro rfl rfl rfl (.nil _)
          have callTyped : ExpressionHasType function.typedBody lexical shape.call.node.id closureType := by
            have typed : ExpressionHasType function.typedBody lexical shape.call.node.id shape.call.node.type := by
              refine .intro (lookupExpression?_sound shape.call.found)
                (shape.callForm ▸ ExpressionFormHasRawType.indirectCall (factoryRead shape.factoryRead) (.cons argumentRead (.nil _)) application)
                shape.call.raw closure (shape.call.type.symm ▸ closure) ?_
              rw [shape.call.requirements, shape.call.coercions, shape.call.type, shape.applicationEq]
              exact .indirectCall (by intro id member; cases member) (.nil _) rfl
            exact Eq.mp (congrArg (fun type => ExpressionHasType function.typedBody lexical shape.call.node.id type) shape.call.type) typed
          have admissible : DataConstructorInstantiation.Admissible lexical shape.instantiation := by
            rw [shape.instantiationEq]
            refine .intro dataType shape.constructor dataMember shape.constructorMember shape.constructorOwner rfl ?_ ?_ ?_ ?_
            · rw [shape.dataParameters]; exact ParameterSubstitution.exact_empty
            · intro parameter replacement member; cases member
            · simp [shape.constructorPayload, payloadTypes, makerType, closureType, convertType, TypeSystem.ParameterSubstitution.apply]
            · simp [shape.dataParameters, ParameterSubstitution.orderedArguments, containerType]
          have constructed := ExpressionFormHasRawType.constructor admissible
            (by rw [shape.instantiationEq]; exact .cons callTyped (.cons priorRead
              (.cons (factoryRead shape.retainedFactoryRead) (.cons convertRead (.nil _)))))
          have resultType : shape.instantiation.resultType = containerType dataType := by rw [shape.instantiationEq]
          rw [resultType] at constructed
          have expressionTyped := shape.expression.ordinary container (shape.expressionForm ▸ constructed)
          exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.statementFound)
            shape.statementForm expressionTyped shape.statementType)⟩

private def typedNode (source : TypedSource) (node : ExpressionNode) (expected : TypeSystem.Ty) :
    IO (TypedNode source expected) := do
  let ⟨found⟩ ← observed (source.lookupExpression? node.id = some node) "typed node occurrence"
  let ⟨raw⟩ ← observed (node.rawType = expected) "typed node raw type"
  let ⟨type⟩ ← observed (node.type = expected) "typed node type"
  let ⟨requirements⟩ ← observed (node.requirements = []) "typed node requirements"
  let ⟨coercions⟩ ← observed (node.coercions = []) "typed node coercions"
  return ⟨node, found, raw, type, requirements, coercions⟩

def readShape (function : CheckedFunction) (signature : ProgramFunctionSignature)
    (dataType : ProgramDataSignature) : IO (ReadShape function signature dataType) := do
  let [factory, argument, prior, convert] := function.typedBody.inputs
    | throw (IO.userError "constructor caller inputs")
  let [.expression argumentNode, .expression factoryNode, .expression callNode, .expression priorNode,
      .expression retainedFactoryNode, .expression convertNode, .expression expressionNode, .statement statement] := function.typedBody.nodes
    | throw (IO.userError "constructor caller nodes")
  let .call _ _ (.indirect application) := callNode.form | throw (IO.userError "constructor indirect child")
  let .constructor instantiation _ := expressionNode.form | throw (IO.userError "constructor parent")
  match constructorFound : dataType.constructors.find? (fun constructor => decide (constructor.id = instantiation.constructor)) with
  | none => throw (IO.userError "constructor catalog entry")
  | some constructor =>
    let argumentRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody argument argumentNode .word
    let factoryRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody factory factoryNode makerType
    let call ← typedNode function.typedBody callNode closureType
    let priorRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody prior priorNode closureType
    let retainedFactoryRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody factory retainedFactoryNode makerType
    let convertRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody convert convertNode convertType
    let expression ← typedNode function.typedBody expressionNode (containerType dataType)
    let ⟨callForm⟩ ← observed (call.node.form = .call factoryRead.node.id [argumentRead.node.id] (.indirect application)) "constructor callForm"
    let ⟨applicationEq⟩ ← observed (application = ⟨1, .word, .word, []⟩) "constructor applicationEq"
    let ⟨constructorOwner⟩ ← observed (constructor.id.dataType = dataType.id) "constructor constructorOwner"
    let ⟨constructorPayload⟩ ← observed (constructor.payloadTypes = payloadTypes) "constructor constructorPayload"
    let ⟨dataParameters⟩ ← observed (dataType.parameters = []) "constructor dataParameters"
    let ⟨instantiationEq⟩ ← observed (instantiation = ⟨constructor.id, [], payloadTypes, containerType dataType⟩) "constructor instantiationEq"
    let ⟨expressionForm⟩ ← observed (expression.node.form = .constructor instantiation [call.node.id, priorRead.node.id, retainedFactoryRead.node.id, convertRead.node.id]) "constructor expressionForm"
    let ⟨factoryScheme⟩ ← observed (factory.scheme = .mono makerType) "constructor factoryScheme"
    let ⟨factoryRequirements⟩ ← observed (factory.schemeRequirements = []) "constructor factoryRequirements"
    let ⟨factoryOrdinary⟩ ← observed (factory.comptime = false) "constructor factoryOrdinary"
    let ⟨argumentScheme⟩ ← observed (argument.scheme = .mono .word) "constructor argumentScheme"
    let ⟨argumentRequirements⟩ ← observed (argument.schemeRequirements = []) "constructor argumentRequirements"
    let ⟨argumentOrdinary⟩ ← observed (argument.comptime = false) "constructor argumentOrdinary"
    let ⟨priorScheme⟩ ← observed (prior.scheme = .mono closureType) "constructor priorScheme"
    let ⟨priorRequirements⟩ ← observed (prior.schemeRequirements = []) "constructor priorRequirements"
    let ⟨priorOrdinary⟩ ← observed (prior.comptime = false) "constructor priorOrdinary"
    let ⟨convertScheme⟩ ← observed (convert.scheme = .mono convertType) "constructor convertScheme"
    let ⟨convertRequirements⟩ ← observed (convert.schemeRequirements = []) "constructor convertRequirements"
    let ⟨convertOrdinary⟩ ← observed (convert.comptime = false) "constructor convertOrdinary"
    let ⟨argumentFactory⟩ ← observed (argument.id ≠ factory.id) "constructor argumentFactory"
    let ⟨priorFactory⟩ ← observed (prior.id ≠ factory.id) "constructor priorFactory"
    let ⟨priorArgument⟩ ← observed (prior.id ≠ argument.id) "constructor priorArgument"
    let ⟨convertFactory⟩ ← observed (convert.id ≠ factory.id) "constructor convertFactory"
    let ⟨convertArgument⟩ ← observed (convert.id ≠ argument.id) "constructor convertArgument"
    let ⟨convertPrior⟩ ← observed (convert.id ≠ prior.id) "constructor convertPrior"
    let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "constructor parameters"
    let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [makerType, .word, closureType, convertType]) "constructor inputTypes"
    let ⟨returns⟩ ← observed (signature.returnTypes = [containerType dataType]) "constructor returns"
    let ⟨inputs⟩ ← observed (function.typedBody.inputs = [factory, argument, prior, convert]) "constructor inputs"
    let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "constructor roots"
    let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "constructor statementFound"
    let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some expression.node.id)) "constructor statementForm"
    let ⟨statementType⟩ ← observed (statement.type = containerType dataType) "constructor statementType"
    return { factory, argument, prior, convert, argumentRead, factoryRead, call, application, priorRead, retainedFactoryRead, convertRead, expression, constructor, instantiation, statement, constructorMember := List.mem_of_find?_eq_some constructorFound, callForm, applicationEq, constructorOwner, constructorPayload, dataParameters, instantiationEq, expressionForm, factoryScheme, factoryRequirements, factoryOrdinary, argumentScheme, argumentRequirements, argumentOrdinary, priorScheme, priorRequirements, priorOrdinary, convertScheme, convertRequirements, convertOrdinary, argumentFactory, priorFactory, priorArgument, convertFactory, convertArgument, convertPrior, parameters, inputTypes, returns, inputs, roots, statementFound, statementForm, statementType }

structure CheckedFixture where
  program : CheckedProgram
  checked : checkProgram workspace 1000 = .ok program
  wellFormed : ProgramWellFormed (Program.ofChecked program)
  makeFunction : CheckedFunction
  readFunction : CheckedFunction
  makeSignature : ProgramFunctionSignature
  readSignature : ProgramFunctionSignature
  functions : program.functions = [makeFunction, readFunction]
  signatures : program.signatures.functions = [makeSignature, readSignature]
  methods : program.methods = []
  makeDeclaration : makeFunction.declaration = makeSignature.id
  readDeclaration : readFunction.declaration = readSignature.id
  distinct : makeSignature.id ≠ readSignature.id
  makeShape : FactoryShape makeFunction makeSignature
  dataType : ProgramDataSignature
  dataMember : dataType ∈ program.signatures.dataTypes
  readShape : ReadShape readFunction readSignature dataType
  makeNodes : makeFunction.typedBody.nodes = [.expression makeShape.read,
    .statement makeShape.innerReturn, .expression makeShape.expression, .statement makeShape.statement]
  readNodes : readFunction.typedBody.nodes = readShape.nodeList

def checkedFixture : IO CheckedFixture := do
  match checked : checkProgram workspace 1000 with
  | .error error => throw (IO.userError (reprStr error))
  | .ok program =>
    match functions : program.functions, signatures : program.signatures.functions with
    | [makeFunction, readFunction], [makeSignature, readSignature] =>
      let makeShape ← shape makeFunction makeSignature
      match dataFound : program.signatures.dataTypes.find? (fun dataType => decide (dataType.name = "Holder")) with
      | none => throw (IO.userError "Holder catalog missing")
      | some dataType =>
       let readShape ← readShape readFunction readSignature dataType
       let ⟨methods⟩ ← observed (program.methods = []) "unexpected methods"
       let ⟨makeDeclaration⟩ ← observed (makeFunction.declaration = makeSignature.id) "make declaration"
       let ⟨readDeclaration⟩ ← observed (readFunction.declaration = readSignature.id) "read declaration"
       let ⟨distinct⟩ ← observed (makeSignature.id ≠ readSignature.id) "distinct declarations"
       let ⟨makeNodes⟩ ← observed (makeFunction.typedBody.nodes = [.expression makeShape.read,
         .statement makeShape.innerReturn, .expression makeShape.expression, .statement makeShape.statement]) "make complete source"
       let ⟨readNodes⟩ ← observed (readFunction.typedBody.nodes = readShape.nodeList) "read complete source"
       let deep : CheckedProgramBodiesHaveStatementTyping program 1000 := {
         functions := by
           intro actual member candidate candidateMember accepted
           have identity := checkFunctionBody_success_declaration accepted
           simp only [functions, List.mem_cons, List.not_mem_nil, or_false] at member
           simp only [signatures, List.mem_cons, List.not_mem_nil, or_false] at candidateMember
           rcases member with rfl | rfl <;> rcases candidateMember with rfl | rfl
           · exact makeShape.statementTyping program.signatures
           · exact False.elim (distinct (makeDeclaration.symm.trans identity))
           · exact False.elim (distinct (identity.symm.trans readDeclaration))
           · exact readShape.statementTyping program.signatures (List.mem_of_find?_eq_some dataFound)
         methods := by intro method member; simp only [methods, List.not_mem_nil] at member }
       return ⟨program, checked, programWellFormed_ofCheckProgram_statements checked deep,
         makeFunction, readFunction, makeSignature, readSignature, functions, signatures, methods,
         makeDeclaration, readDeclaration, distinct, makeShape, dataType, List.mem_of_find?_eq_some dataFound, readShape, makeNodes, readNodes⟩
    | _, _ => throw (IO.userError "captured reuse declaration count")

end Tests.SourceCoreConstructorCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreConstructorCallsFixture
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreConstructorCalls
open Solcore Frontend SourceInference SourceSemantics

structure CompiledFixture extends CheckedFixture where
  seeds : List SourceCompiler.Seed
  options : SourceCompiler.Options
  facadeCompiled : SourceCompiler.Compiled
  accepted : SourceCompiler.compileChecked program seeds options = .ok facadeCompiled
  recipe : SourceCoreIndexedSession.Recipe
  issued : CoreLowering.RecursiveNamedPreparedStageContracts.PublicRecipe facadeCompiled recipe
  sameProgram : recipe.compiled.sourceProgram = program
  recipePrepared : SourceCoreIndexedSession.Recipe.prepare recipe.compiled = .ok recipe

def compiledFixture : IO CompiledFixture := do
  let checked ← checkedFixture
  let seeds := [SourceCompiler.Seed.declaration checked.makeSignature.id,
    SourceCompiler.Seed.declaration checked.readSignature.id]
  let options : SourceCompiler.Options := {checkingFuel := 1000, compilationFuel := 100}
  match generated : SourceCoreCompiler.compileChecked checked.program seeds options with
  | .error error => throw (IO.userError (reprStr error))
  | .ok source =>
    match selected : source.artifact? with
    | none => throw (IO.userError "factory cached artifact missing")
    | some cached =>
      match prepared : SourceCoreIndexedSession.Recipe.prepare cached with
      | .error error => throw (IO.userError (reprStr error))
      | .ok recipe =>
        match facade : SourceCoreExecution.prepare source with
        | .error error => throw (IO.userError (reprStr error))
        | .ok facadeCompiled =>
          have accepted : SourceCompiler.compileChecked checked.program seeds options = .ok facadeCompiled := by
            simpa only [SourceCoreExecution.compileChecked, generated, Except.mapError,
              bind, Except.bind] using facade
          have sameProgram : recipe.compiled.sourceProgram = checked.program :=
            (congrArg (·.sourceProgram) (SourceCoreIndexedSession.Recipe.prepare_compiled prepared)).trans
              ((source.artifact_fields selected).1.trans (SourceCoreCompiler.compileChecked_program generated))
          return {
            toCheckedFixture := checked
            seeds := seeds
            options := options
            facadeCompiled := facadeCompiled
            accepted := accepted
            recipe := recipe
            issued := CoreLowering.RecursiveNamedPreparedStageContracts.public_preparation selected prepared facade
            sameProgram := sameProgram
            recipePrepared := by rw [SourceCoreIndexedSession.Recipe.prepare_compiled prepared]; exact prepared }

theorem CompiledFixture.prepared (fixture : CompiledFixture)
    {row : SourceSpecialization.SpecializedFunction}
    (member : row ∈ fixture.recipe.compiled.validationPlan.specializations) :
    Nonempty (CoreLowering.RecursiveNamedPublicSpecializationMeaning.Prepared fixture.recipe.compiled row) :=
  CoreLowering.RecursiveNamedPublicSpecializationMeaning.of_public_compile fixture.accepted fixture.issued member

theorem CompiledFixture.source_wellFormed (fixture : CompiledFixture) :
    ProgramWellFormed (Program.ofChecked fixture.recipe.compiled.sourceProgram) := by
  rw [fixture.sameProgram]
  exact fixture.wellFormed

structure ActualHeader (fixture : CompiledFixture) (row : SourceSpecialization.SpecializedFunction) where
  prepared : CoreLowering.RecursiveNamedPublicSpecializationMeaning.Prepared fixture.recipe.compiled row
  header : CoreLowering.CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
    (Program.ofChecked fixture.recipe.compiled.sourceProgram)
  aligned : CoreLowering.RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared
    (CoreLowering.CallableNamedMetadata.instantiation row) header
  diagnostic : CoreLowering.CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared



open CoreLowering

theorem ActualHeader.terminal {fixture : CompiledFixture} {row : SourceSpecialization.SpecializedFunction}
    (actual : ActualHeader fixture row) (expression : ExpressionId) (statement : StatementNode)
    (roots : row.function.typedBody.roots = [.statement statement.id])
    (found : row.function.typedBody.lookupStatement? statement.id = some statement)
    (form : statement.form = .returnStmt (some expression)) :
    ∃ terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header,
      CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared ∧
      terminal.expression = expression ∧ terminal.certificate =
        CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
          (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
          terminal.expression terminal.receipt.child := by
  have source : actual.header.function.source = row.function.typedBody := by
    rw [actual.aligned.function]
    exact congrArg (fun specialized => specialized.function.typedBody) actual.prepared.same
  have body : actual.header.function.body = [statement.id] := by
    rw [actual.aligned.function]
    change actual.prepared.compilation.statements = [statement.id]
    have accepted := actual.prepared.compilation.roots
    change (actual.prepared.named.specialized.function.typedBody.roots.mapM _) = _ at accepted
    rw [actual.prepared.same, roots] at accepted
    exact (Except.ok.inj accepted).symm
  have terminalShape : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      actual.header.function.source expression actual.header.function.body := by
    rw [source, body]
    exact .returning [] found form
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    (by rw [actual.aligned.policy]; rfl) terminalShape actual.aligned.accepted
  let terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header := {
    row := row
    prepared := actual.prepared
    instantiation := CallableNamedMetadata.instantiation row
    aligned := actual.aligned
    layouts := actual.aligned.layouts
    expression := expression
    receipt := receipt
    certificate := CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
      (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression receipt.child
    certifies := by
      intro child generated
      have same : child = receipt.child := Except.ok.inj (generated.symm.trans receipt.generated)
      exact ⟨rfl, rfl, same⟩ }
  exact ⟨terminal, actual.diagnostic, rfl, rfl⟩



/-- Each observation refers to an actual compiler row, unique physical slot,
entry, and original source declaration. No semantic body certificate is supplied. -/
structure ObservedRow (fixture : CompiledFixture) (signature : ProgramFunctionSignature) where
  row : SourceSpecialization.SpecializedFunction
  member : row ∈ fixture.recipe.compiled.validationPlan.specializations
  sourceOwner : row.function.typedBody.owner = signature.id
  parameters : row.parameterSubstitution = []
  ordinary : row.function.returnComptime = false
  inputsOrdinary : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false
  target : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
    (CallableNamedMetadata.instantiation row) = .ok row.key
  global : SourceCoreCalls.Signature
  index : Nat
  slot : CallableNamedMetadata.Slot fixture.recipe.compiled.indexed.base.globals index global
  globalKey : global.key = row.key
  entry : SourceCoreCallableIndexedPrograms.Entry fixture.recipe.compiled.indexed.layouts
  entryMember : entry ∈ fixture.recipe.compiled.indexed.entries
  entryKey : entry.key = row.key

private def observeTarget (fixture : CompiledFixture) (row : SourceSpecialization.SpecializedFunction) :
    IO (PLift (SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) = .ok row.key)) := do
  match accepted : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) with
  | .error error => throw (IO.userError (reprStr error))
  | .ok key =>
    let ⟨same⟩ ← observed (key = row.key) "reuse exact key"
    return ⟨by rw [accepted, same]⟩

def observeRow (fixture : CompiledFixture) (signature : ProgramFunctionSignature) :
    IO (ObservedRow fixture signature) := do
  match found : fixture.recipe.compiled.validationPlan.specializations.find?
      (fun row => decide (row.function.typedBody.owner = signature.id)) with
  | none => throw (IO.userError "reuse specialization missing")
  | some row =>
    let ⟨sourceOwner⟩ ← observed (row.function.typedBody.owner = signature.id) "reuse source owner"
    let ⟨parameters⟩ ← observed (row.parameterSubstitution = []) "reuse substitution"
    let ⟨ordinary⟩ ← observed (row.function.returnComptime = false) "reuse return marker"
    let ⟨ordinaryInputs⟩ ← observed (row.function.typedBody.inputs.all (fun binder => !binder.comptime) = true) "reuse parameter markers"
    let ⟨target⟩ ← observeTarget fixture row
    match slot : fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun item => decide (item.1.key = row.key)) with
    | [(global, index)] =>
      let ⟨globalKey⟩ ← observed (global.key = row.key) "reuse global key"
      match entryFound : fixture.recipe.compiled.indexed.entries.find? (fun entry => decide (entry.key = row.key)) with
      | none => throw (IO.userError "reuse entry missing")
      | some entry =>
        let ⟨entryKey⟩ ← observed (entry.key = row.key) "reuse entry key"
        return {
          row := row
          member := List.mem_of_find?_eq_some found
          sourceOwner := sourceOwner
          parameters := parameters
          ordinary := ordinary
          inputsOrdinary := by
            intro binder member
            have selected := List.all_eq_true.mp ordinaryInputs binder member
            cases same : binder.comptime <;> simp_all
          target := target
          global := global
          index := index
          slot := by unfold CallableNamedMetadata.Slot; rw [globalKey]; exact slot
          globalKey := globalKey
          entry := entry
          entryMember := List.mem_of_find?_eq_some entryFound
          entryKey := entryKey }
    | _ => throw (IO.userError "reuse unique global slot")

structure ObservedProgram (fixture : CompiledFixture) where
  makeRow : ObservedRow fixture fixture.makeSignature
  readRow : ObservedRow fixture fixture.readSignature
  globalsLength : fixture.recipe.compiled.indexed.base.globals.length = 2
  distinctSlots : makeRow.index ≠ readRow.index
  makeShape : FactoryShape makeRow.row.function fixture.makeSignature
  readShape : ReadShape readRow.row.function fixture.readSignature fixture.dataType
  makeNodes : makeRow.row.function.typedBody.nodes = [.expression makeShape.read,
    .statement makeShape.innerReturn, .expression makeShape.expression, .statement makeShape.statement]
  readNodes : readRow.row.function.typedBody.nodes = readShape.nodeList
  noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []
  profile : fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true

def observeProgram (fixture : CompiledFixture) : IO (ObservedProgram fixture) := do
  let makeRow ← observeRow fixture fixture.makeSignature
  let readRow ← observeRow fixture fixture.readSignature
  let makeShape ← shape makeRow.row.function fixture.makeSignature
  let readShape ← readShape readRow.row.function fixture.readSignature fixture.dataType
  let ⟨globalsLength⟩ ← observed (fixture.recipe.compiled.indexed.base.globals.length = 2) "reuse global count"
  let ⟨distinctSlots⟩ ← observed (makeRow.index ≠ readRow.index) "reuse distinct slots"
  let ⟨makeNodes⟩ ← observed (makeRow.row.function.typedBody.nodes = [.expression makeShape.read,
    .statement makeShape.innerReturn, .expression makeShape.expression, .statement makeShape.statement]) "reuse make nodes"
  let ⟨readNodes⟩ ← observed (readRow.row.function.typedBody.nodes = readShape.nodeList) "reuse read nodes"
  let ⟨noLocals⟩ ← observed (fixture.recipe.compiled.indexed.base.locals.bindings = []) "reuse local catalog"
  let ⟨profile⟩ ← observed (fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true) "reuse callable profile"
  return {
    makeRow := makeRow
    readRow := readRow
    globalsLength := globalsLength
    distinctSlots := distinctSlots
    makeShape := makeShape
    readShape := readShape
    makeNodes := makeNodes
    readNodes := readNodes
    noLocals := noLocals
    profile := profile }


/-- The actual unique global slot identifies the complete prepared signature
and index, without choosing a new prepared row. -/
theorem ObservedRow.prepared_slot {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    (observed : ObservedRow fixture signature)
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared fixture.recipe.compiled observed.row) :
    prepared.named.signature = observed.global ∧ prepared.index = observed.index := by
  have selected := CallableIndexedPreparedInventories.cached_global_at fixture.recipe.compiled prepared.selected
  have member : (prepared.named.signature, prepared.index) ∈
      fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun item => decide (item.1.key = observed.global.key)) := by
    refine List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr selected, ?_⟩
    simp only [observed.globalKey, RecursiveNamedPreparedCallEvidence.Prepared.signature_key prepared,
      decide_true]
  rw [observed.slot] at member
  exact Prod.mk.inj (List.mem_singleton.mp member)

/-- Issue exactly one authentic Header with its matching diagnostic receipt. -/
theorem ObservedRow.issue {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    (observed : ObservedRow fixture signature) :
    ∃ input : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled,
      input.row = observed.row ∧
      ∃ packet : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued input,
      ∃ actual : ActualHeader fixture observed.row,
        actual.header = packet.header ∧ actual.header.slot = observed.index ∧
        actual.header.named.signature = observed.global := by
  obtain ⟨prepared⟩ := fixture.prepared observed.member
  obtain ⟨signatureEq, indexEq⟩ := observed.prepared_slot prepared
  have range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures fixture.recipe.compiled.sourceProgram.signatures) observed.row.parameterSubstitution := by
    simp only [observed.parameters, SourceSemantics.ParameterSubstitution.RangeWellFormed,
      List.not_mem_nil, false_implies, implies_true]
  have metadata : CallableNamedCanonicalOrder.retainedInstantiation observed.row =
      CallableNamedMetadata.instantiation observed.row := by
    simp [CallableNamedCanonicalOrder.retainedInstantiation, CallableNamedMetadata.instantiation, observed.parameters]
  let input : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled := {
    row := observed.row
    prepared := prepared
    range := range
    ordinaryReturn := observed.ordinary
    ordinaryParameters := observed.inputsOrdinary
    target := by
      rw [metadata, RecursiveNamedPreparedCallEvidence.Prepared.signature_key prepared]
      exact observed.target
    slot := by rw [signatureEq, indexEq]; exact observed.slot }
  obtain ⟨packet⟩ := CallableIndexedOwnedPreparedFiniteNamedInventories.issue fixture.source_wellFormed input
  let actual : ActualHeader fixture observed.row := {
    prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued prepared packet.selected
    header := packet.header
    aligned := by simpa only [input, metadata] using packet.aligned
    diagnostic := ⟨⟨packet.selected.diagnostics, packet.selected.found, rfl⟩⟩ }
  exact ⟨input, rfl, packet, actual, rfl, actual.aligned.slot.trans indexEq,
    (congrArg (·.signature) actual.aligned.named).trans signatureEq⟩

/-- Both real issuer packets cover every physical global slot. -/
theorem ObservedProgram.inventory {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    ∃ (makeInput readInput : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled),
      makeInput.row = observed.makeRow.row ∧ readInput.row = observed.readRow.row ∧
      ∃ (makePacket : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued makeInput)
        (readPacket : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued readInput),
      ∃ (makeHeader : ActualHeader fixture observed.makeRow.row)
        (readHeader : ActualHeader fixture observed.readRow.row),
        makeHeader.header = makePacket.header ∧ readHeader.header = readPacket.header ∧
        RecursiveNamedCatalogNativeContexts.Complete
          (values := .initial fixture.recipe.compiled.compatible.checked)
          (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
          (CallableIndexedOwnedPreparedFiniteNamedInventories.headers (.cons makePacket (.cons readPacket .nil))) := by
  obtain ⟨makeInput, makeRow, makePacket, makeHeader, makeEq, makeSlot, makeSignature⟩ := observed.makeRow.issue
  obtain ⟨readInput, readRow, readPacket, readHeader, readEq, readSlot, readSignature⟩ := observed.readRow.issue
  refine ⟨makeInput, readInput, makeRow, readRow, makePacket, readPacket, makeHeader, readHeader,
    makeEq, readEq, ?_⟩
  have makeBound := (List.getElem?_eq_some_iff.mp observed.makeRow.slot.selected).1
  have readBound := (List.getElem?_eq_some_iff.mp observed.readRow.slot.selected).1
  rw [observed.globalsLength] at makeBound readBound
  intro index signature found
  have bound := (List.getElem?_eq_some_iff.mp found).1
  rw [observed.globalsLength] at bound
  have casesIndex : index = observed.makeRow.index ∨ index = observed.readRow.index := by
    have distinct := observed.distinctSlots
    omega
  rcases casesIndex with same | same
  · refine ⟨makeHeader.header, ?_, makeSlot.trans same.symm, ?_⟩
    · rw [makeEq]; exact .head _
    · rw [same, observed.makeRow.slot.selected] at found
      exact makeSignature.trans (Option.some.inj found)
  · refine ⟨readHeader.header, ?_, readSlot.trans same.symm, ?_⟩
    · rw [readEq]; exact .tail _ (.head _)
    · rw [same, observed.readRow.slot.selected] at found
      exact readSignature.trans (Option.some.inj found)


structure ObservedStages (fixture : CompiledFixture)
    {signature : ProgramFunctionSignature} (observed : ObservedRow fixture signature) where
  descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named observed.row.key)
  native : SourceCoreGeneralFunctions.CallableContext
  present : fixture.recipe.compiled.indexed.base.callableContext = some native
  sidecar : SourceCoreStageContracts.Sidecar
  issued : SourceCoreStageContracts.prepareSidecar
    fixture.recipe.compiled.indexed.base.plan observed.row.key = .ok sidecar

def observeStages (fixture : CompiledFixture) {signature : ProgramFunctionSignature} (observed : ObservedRow fixture signature) :
    IO (ObservedStages fixture observed) := do
  match present : fixture.recipe.compiled.indexed.base.callableContext with
  | none => throw (IO.userError "factory callable context missing")
  | some native =>
    match issued : SourceCoreStageContracts.prepareSidecar
        fixture.recipe.compiled.indexed.base.plan observed.row.key with
    | .error _ => throw (IO.userError "factory original sidecar missing")
    | .ok sidecar =>
      match SourceCoreCallableContracts.descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
          (.named observed.row.key) with
      | .error error => throw (IO.userError (reprStr error))
      | .ok descriptor => return ⟨descriptor, native, present, sidecar, issued⟩

def ObservedStages.registry {fixture : CompiledFixture} {signature : ProgramFunctionSignature} {observed : ObservedRow fixture signature}
    (_actual : ObservedStages fixture observed) : Staging.Recursive.Registry :=
  RecursiveNamedPreparedStageScopes.registry
    (RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected)

theorem ObservedStages.selected {fixture : CompiledFixture} {signature : ProgramFunctionSignature} {observed : ObservedRow fixture signature}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    stages.registry.Closure actual.header.function
      (RecursiveStageRegistry.scope stages.sidecar [] actual.header.function) := by
  have same := RecursiveNamedPreparedStageScopes.sidecar_caller stages.issued
    (CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.record actual.prepared actual.aligned)
  rw [actual.aligned.function]
  exact RecursiveNamedPreparedStageScopes.Selected.named actual.prepared stages.sidecar stages.issued same


theorem bootstrap_zero (compiled : SourceCoreUnifiedCompilation.Compiled)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey
      (CallableIndexedOwnedPreparedBootstrapRootState.keys compiled)) :
    owner.key.capturePrefix = 0 := by
  have bound := owner.position.isLt
  change owner.position.val < 1 at bound
  have zero : owner.position.val = 0 := by omega
  simp only [CallableIndexedOwnedFunctionValues.OwnedKey.key,
    CallableIndexedOwnedPreparedBootstrapRootState.keys,
    CallableIndexedOwnedPreparedBootstrapRootState.key, zero, List.getElem_cons_zero]

theorem ActualHeader.source {fixture : CompiledFixture} {row : SourceSpecialization.SpecializedFunction}
    (actual : ActualHeader fixture row) : actual.header.function.source = row.function.typedBody := by
  rw [actual.aligned.function]
  exact congrArg (fun row => row.function.typedBody) actual.prepared.same

def seed : Core.Word := Core.Word.ofNatModulo 10

def runOptions : SourceCoreExecution.RunOptions := {
  executionFuel := 100000
  inputValidationFuel := 1000
  outputValidationFuel := 1000 }

/-- Concrete public execution retains the original opened artifact, fresh
bootstrap and exact run receipt. Its exported handle is not manufactured. -/
structure ObservedPublicRun (fixture : CompiledFixture) {signature : ProgramFunctionSignature} (observed : ObservedRow fixture signature) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facadeCompiled
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start observed.row.key [.word seed] runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion artifact
  executed : session.RunAt observed.row.key [.word seed] runOptions (.ok (.succeeded completion))
  handle : SourceCorePublicValues.Handle
  returned : completion.value = .function handle

def observePublicRun (fixture : CompiledFixture) {signature : ProgramFunctionSignature} (observed : ObservedRow fixture signature) :
    IO (ObservedPublicRun fixture observed) := do
  let opened ← fixture.facadeCompiled.openWithReceipt
  let fresh ← opened.val.bootstrapWithExportReceipt
  match ready : fresh.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "factory bootstrap exhausted")
  | .ready session =>
    match started : session.start observed.row.key [.word seed] runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint =>
      let executed ← session.runWithReceipt observed.row.key [.word seed] runOptions
      match result : executed.val with
      | .error error => throw (IO.userError (reprStr error))
      | .ok (.failed _ _) => throw (IO.userError "factory public run failed")
      | .ok (.exportError error _) => throw (IO.userError (reprStr error))
      | .ok (.outOfFuel _) => throw (IO.userError "factory public run exhausted")
      | .ok (.succeeded completion) =>
        match returned : completion.value with
        | .function handle =>
          return ⟨opened.val, opened.property, fresh.val, fresh.property.1, fresh.property.2, session, ready,
            checkpoint, started, completion, result ▸ executed.property, handle, returned⟩
        | _ => throw (IO.userError "factory output was not a function handle")


/-- The complete checked read body contains no anonymous function occurrence. -/
theorem ObservedProgram.read_no_lambda {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) :
    ∀ id node, ContainsExpression observed.readRow.row.function.typedBody id node →
      ∀ parameters result body, node.form ≠ .lambda parameters result body := by
  intro id node present parameters result body form
  have member := present.1
  rw [observed.readNodes, ReadShape.nodeList] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same | same | same | same | same | same
  all_goals try cases same
  · rw [observed.readShape.argumentRead.form] at form; cases form
  · rw [observed.readShape.factoryRead.form] at form; cases form
  · rw [observed.readShape.callForm] at form; cases form
  · rw [observed.readShape.priorRead.form] at form; cases form
  · rw [observed.readShape.retainedFactoryRead.form] at form; cases form
  · rw [observed.readShape.convertRead.form] at form; cases form
  · rw [observed.readShape.expressionForm] at form; cases form


private theorem recipe_unique {compiled : SourceCoreExecution.Compiled}
    {first second : SourceCoreIndexedSession.Recipe}
    (left : RecursiveNamedPreparedStageContracts.PublicRecipe compiled first)
    (right : RecursiveNamedPreparedStageContracts.PublicRecipe compiled second) : first = second := by
  cases compiled
  exact Option.some.inj (left.symm.trans right)

/-- Any later actual public startup on this compiled artifact recovers its
same recipe, exact indexed session, checkpoint, input encoding and store. -/
theorem CompiledFixture.actual_start (fixture : CompiledFixture)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {key : SourceSpecialization.SpecializationKey} {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    (opened : publicArtifact.CompiledAt fixture.facadeCompiled)
    (started : publicSession.start key arguments fuel = .ok publicCheckpoint) :
    ∃ (artifact : SourceCoreIndexedSession.Artifact)
      (session : SourceCoreIndexedSession.Session artifact)
      (checkpoint : SourceCoreIndexedSession.Checkpoint artifact)
      (root : SourceCoreIndexedSession.Root fixture.recipe.compiled)
      (world : Core.StoreTyping) (store : Core.Store) (native : Core.Environment)
      (encodedValues : SourceCoreCompatibleValues.Context),
      publicArtifact.IndexedAt fixture.facadeCompiled fixture.recipe artifact ∧
      SourceCoreIndexedSession.Recipe.prepare fixture.recipe.compiled = .ok fixture.recipe ∧
      publicSession.IndexedAt session ∧ publicCheckpoint.IndexedAt checkpoint ∧
      RecursiveNamedPublicStartMeaning.StartAt session key arguments fuel
        checkpoint fixture.recipe root world store native encodedValues := by
  obtain ⟨recipe, artifact, session, checkpoint, root, world, store, native, encodedValues,
      atArtifact, prepared, _program, sessionAt, checkpointAt, startReceipt⟩ :=
    RecursiveNamedPublicExecutionMeaning.actual_start fixture.accepted opened started
  have same := recipe_unique atArtifact.compiled_recipe fixture.issued
  cases same
  exact ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
    atArtifact, prepared, sessionAt, checkpointAt, startReceipt⟩

end Tests.SourceCoreConstructorCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreConstructorCallsMakeSupport
/-! Concrete make support and the complete closure family for the two-function
checked program. The actual compiler observations produce every body premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreConstructorCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering

structure ObservedMake (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  owned : observed.makeShape.expression.id.occurrence.owner = observed.makeRow.row.function.typedBody.owner
  reported : Core.Ty
  read : SourceCoreCompatibleDataExpressions.readExpression fixture.recipe.compiled.compatible.checked
    observed.makeRow.row.function.typedBody observed.makeShape.expression.id = .ok (observed.makeShape.expression, reported)
  binderScheme : observed.makeShape.binder.scheme = .mono .word

private def confirm (proposition : Prop) [Decidable proposition] (label : String) : IO (PLift proposition) := do
  if accepted : proposition then return ⟨accepted⟩
  else throw (IO.userError label)

def observeMake (fixture : CompiledFixture) (observed : ObservedProgram fixture) : IO (ObservedMake fixture observed) := do
  let ⟨owned⟩ ← confirm (observed.makeShape.expression.id.occurrence.owner = observed.makeRow.row.function.typedBody.owner) "reuse lambda owner"
  let ⟨binderScheme⟩ ← confirm (observed.makeShape.binder.scheme = .mono .word) "reuse seed type"
  match read : SourceCoreCompatibleDataExpressions.readExpression fixture.recipe.compiled.compatible.checked
      observed.makeRow.row.function.typedBody observed.makeShape.expression.id with
  | .error error => throw (IO.userError (reprStr error))
  | .ok (node, reported) =>
    let ⟨same⟩ ← confirm (node = observed.makeShape.expression) "reuse exact lambda read"
    return ⟨owned, reported, by simpa only [same] using read, binderScheme⟩

theorem ActualHeader.make_formation {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (extra : ObservedMake fixture observed) (stages : ObservedStages fixture observed.makeRow)
    (actual : ActualHeader fixture observed.makeRow.row)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (expression : terminal.expression = observed.makeShape.expression.id)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} :
    Nonempty (CallableIndexedOwnedContextualLambdaFormationReceipts.OrdinaryFormation
      (registry := registry) (faults := faults) actual.header actual.header.context
      actual.header.function.evidence
      (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) := by
  apply CallableIndexedOwnedPreparedNamedReturnLambdaFormation.of_terminal terminal
    fixture.recipePrepared diagnostic fixture.source_wellFormed observed.profile (stages.selected actual)
    observed.makeRow.entryMember
    (node := observed.makeShape.expression) (reported := extra.reported)
  · rw [actual.source, expression]; exact observed.makeShape.expressionFound
  · exact observed.makeShape.lambda
  · rw [actual.source, expression]; exact extra.owned
  · exact observed.makeShape.requirements
  · exact observed.makeShape.coercions
  · simp only [observed.noLocals, List.find?_nil]
  · rw [actual.source, expression]; exact extra.read
  · rw [actual.source]; exact observed.makeShape.innerReturnFound
  · exact observed.makeShape.innerReturnForm
  · exact observed.makeShape.innerReturnType

theorem ActualHeader.make_support {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (extra : ObservedMake fixture observed) (stages : ObservedStages fixture observed.makeRow)
    (actual : ActualHeader fixture observed.makeRow.row)
    (headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)))
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) headers)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (expression : terminal.expression = observed.makeShape.expression.id)
    (point : terminal.certificate = CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
      (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedBodySupport.Support headers
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry actual.header stages.registry terminal faults) := by
  obtain ⟨formation⟩ := actual.make_formation extra stages terminal diagnostic expression
  exact ⟨.formation (CallableIndexedOwnedPreparedStagedNamedBodySupport.Formation.of_actual headers
    (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
    registry actual.header stages.registry terminal faults point complete
    (bootstrap_zero fixture.recipe.compiled) formation fixture.source_wellFormed)⟩

theorem ObservedProgram.cached_source {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (readHeader : ActualHeader fixture observed.readRow.row)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : fixture.recipe.compiled.indexed.base.functions[index]? = some named) :
    CallableIndexedNamedGeneration.source named = observed.makeRow.row.function.typedBody ∨
    CallableIndexedNamedGeneration.source named = observed.readRow.row.function.typedBody := by
  have length : fixture.recipe.compiled.indexed.base.functions.length = 2 := by
    simpa only [CallableIndexedPreparedInventories.cached_globals, List.length_map] using observed.globalsLength
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  rw [length] at bound
  have makeBound := (List.getElem?_eq_some_iff.mp observed.makeRow.slot.selected).1
  have readBound := (List.getElem?_eq_some_iff.mp observed.readRow.slot.selected).1
  rw [observed.globalsLength] at makeBound readBound
  have casesIndex : index = observed.makeRow.index ∨ index = observed.readRow.index := by
    have distinct := observed.distinctSlots
    omega
  rcases casesIndex with same | same
  · left
    have actualIndex := (observed.makeRow.prepared_slot makeHeader.prepared).2
    rw [same, ← actualIndex, makeHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) makeHeader.prepared.same
  · right
    have actualIndex := (observed.readRow.prepared_slot readHeader.prepared).2
    rw [same, ← actualIndex, readHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) readHeader.prepared.same

theorem ObservedProgram.make_lambda_shape {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {body : List StatementId}
    (found : observed.makeRow.row.function.typedBody.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result body) :
    parameters = [] ∧ result = .word ∧ body = [observed.makeShape.innerReturn.id] := by
  have member := (lookupExpression?_sound found).1
  rw [observed.makeNodes] at member
  rcases List.mem_cons.mp member with same | rest
  · have nodeEq := Node.expression.inj same
    rw [nodeEq, observed.makeShape.readForm] at form
    cases form
  · rcases List.mem_cons.mp rest with impossible | rest
    · cases impossible
    · rcases List.mem_cons.mp rest with same | rest
      · have nodeEq := Node.expression.inj same
        rw [nodeEq, observed.makeShape.lambda] at form
        obtain ⟨parametersEq, resultEq, bodyEq⟩ := ExpressionForm.lambda.inj form
        exact ⟨parametersEq.symm, resultEq.symm, bodyEq.symm⟩
      · rcases List.mem_cons.mp rest with impossible | empty
        · cases impossible
        · cases empty

theorem CompiledFixture.no_principal (fixture : CompiledFixture)
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal fixture.recipe.compiled method) : False := by
  obtain ⟨_implementation, _method, _trait, _definition, _substitution, instantiated⟩ := principal.source_instantiation
  cases instantiated with
  | intro _ _ _ _ member _ _ _ _ _ _ _ =>
    simp only [Program.ofChecked, fixture.sameProgram, fixture.methods, List.map_nil,
      List.not_mem_nil] at member

def ObservedProgram.family {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (readHeader : ActualHeader fixture observed.readRow.row)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    {registry : SourceCoreRawMetadata.Registry}
    {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association headers
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      mapping world function native bindings parameter result) :
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor stagePrepared association := by
  cases association with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
    apply CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor.sequence
    have sameSource : function.source = observed.makeRow.row.function.typedBody := by
      rcases observed.cached_source makeHeader readHeader support.caller.selected with original | original
      · exact support.source.trans original
      · have found := code.sourceFound
        rw [support.source.trans original] at found
        exact False.elim (observed.read_no_lambda _ _ (lookupExpression?_sound found) _ _ _ code.sourceForm)
    have found := code.sourceFound
    rw [sameSource] at found
    have bodyShape := (observed.make_lambda_shape found code.sourceForm).2.2
    exact CallableIndexedOwnedPreparedStagedSingleReadSequence.sequence stagePrepared code support provenance
      receiver fixture.source_wellFormed
      (by rw [sameSource]; exact observed.makeNodes) observed.makeShape.lambda bodyShape
      (by rw [sameSource]; exact observed.makeShape.innerReturnFound) observed.makeShape.innerReturnForm
      (by rw [sameSource]; exact observed.makeShape.readFound) observed.makeShape.readForm
      observed.makeShape.readRequirements observed.makeShape.readCoercions observed.noLocals
      fixture.makeSignature (by rw [fixture.sameProgram, fixture.signatures]; exact .head _)
      (by rw [sameSource]; exact observed.makeRow.sourceOwner)
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    exact False.elim (fixture.no_principal support.principal)


theorem ActualHeader.make_input_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (extra : ObservedMake fixture observed) (actual : ActualHeader fixture observed.makeRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.word] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.makeShape.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    extra.binderScheme, TypeSystem.Scheme.mono] using inputs.symm

def ActualHeader.descriptor {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    {observed : ObservedRow fixture signature}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named actual.header.named.signature.key) := by
  rw [actual.aligned.named, RecursiveNamedPreparedCallEvidence.Prepared.signature_key actual.prepared]
  exact stages.descriptor

end Tests.SourceCoreConstructorCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreConstructorCallsInventory
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreConstructorCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
theorem actualStagePrepared (fixture : CompiledFixture) :
    RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable :=
  RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
    fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected

structure ObservedReceiver (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics
  registry : completion.result.context.registry = fixture.recipe.compiled.compatible.checked.staticRegistry

/-- The receiver is built directly at the genuine initial metadata registry. -/
theorem initial_receiver (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    Nonempty (ObservedReceiver fixture observed) := by
  obtain ⟨receiver, _entry, registry, issued⟩ :=
    CallableIndexedOwnedPublicFaultReceivers.Receiver.at_registry fixture.recipe.compiled observed.makeRow.entry
      fixture.recipe.compiled.compatible.checked.staticRegistry (.refl _)
  exact ⟨⟨receiver, issued, registry⟩⟩


structure OrdinaryInventory (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    where
  makeInput : Input fixture.recipe.compiled
  readInput : Input fixture.recipe.compiled
  makeRow : makeInput.row = observed.makeRow.row
  readRow : readInput.row = observed.readRow.row
  makePacket : Issued makeInput
  readPacket : Issued readInput
  makeHeader : ActualHeader fixture observed.makeRow.row
  readHeader : ActualHeader fixture observed.readRow.row
  makeEq : makeHeader.header = makePacket.header
  readEq : readHeader.header = readPacket.header
  rows : Inventory [makeInput, readInput]
  rowsEq : rows = .cons makePacket (.cons readPacket .nil)
  complete : RecursiveNamedCatalogNativeContexts.Complete
    (values := .initial fixture.recipe.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) (headers rows)
  distinct : ([makeInput, readInput].map (fun input => input.prepared.index)).Nodup
  slotsDistinct : makeHeader.header.slot ≠ readHeader.header.slot
  makeDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named makeHeader.header.named.signature.key)
  readDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named readHeader.header.named.signature.key)

theorem ordinary_inventory (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (makeStages : ObservedStages fixture observed.makeRow)
    (readStages : ObservedStages fixture observed.readRow)
    : Nonempty (OrdinaryInventory fixture observed) := by
  obtain ⟨makeInput, readInput, makeRow, readRow, makePacket, readPacket,
    makeHeader, readHeader, makeEq, readEq, complete⟩ := observed.inventory
  let rows : Inventory [makeInput, readInput] := .cons makePacket (.cons readPacket .nil)
  have headerList : headers rows = [makeHeader.header, readHeader.header] := by
    simp only [rows, headers, makeEq, readEq]
  have makeIndex : makeHeader.header.slot = observed.makeRow.index :=
    makeHeader.aligned.slot.trans (observed.makeRow.prepared_slot makeHeader.prepared).2
  have readIndex : readHeader.header.slot = observed.readRow.index :=
    readHeader.aligned.slot.trans (observed.readRow.prepared_slot readHeader.prepared).2
  have slotsDistinct : makeHeader.header.slot ≠ readHeader.header.slot := by
    rw [makeIndex, readIndex]
    exact observed.distinctSlots
  have inputDistinct : makeInput.prepared.index ≠ readInput.prepared.index := by
    have left : makeHeader.header.slot = makeInput.prepared.index := by
      rw [makeEq]; exact makePacket.aligned.slot
    have right : readHeader.header.slot = readInput.prepared.index := by
      rw [readEq]; exact readPacket.aligned.slot
    rw [← left, ← right]
    exact slotsDistinct
  exact ⟨{
    makeInput := makeInput
    readInput := readInput
    makeRow := makeRow
    readRow := readRow
    makePacket := makePacket
    readPacket := readPacket
    makeHeader := makeHeader
    readHeader := readHeader
    makeEq := makeEq
    readEq := readEq
    rows := rows
    rowsEq := rfl
    complete := complete
    distinct := by simp [inputDistinct]
    slotsDistinct := slotsDistinct
    makeDescriptor := makeHeader.descriptor makeStages
    readDescriptor := readHeader.descriptor readStages }⟩

end Tests.SourceCoreConstructorCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreConstructorCallsProgramCertificate
/-! The original constructor calls program is admitted once from its complete actual
cache. A finite row check selects the existing two-header order; it does not
construct syntax, metadata, closure support or method body support. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreConstructorCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

structure ObservedProgramCertificate (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  certificate : CallableIndexedOwnedPreparedProgramAdmission.Certificate fixture.recipe.compiled
  accepted : CallableIndexedOwnedPreparedProgramAdmission.certify fixture.recipe.compiled
    fixture.source_wellFormed 64 = some certificate
  rows : ∀ row ∈ certificate.table.rows, row ∈ [observed.makeRow.row, observed.readRow.row]

def observeProgramCertificate (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedProgramCertificate fixture observed) := do
  match accepted : CallableIndexedOwnedPreparedProgramAdmission.certify fixture.recipe.compiled
      fixture.source_wellFormed 64 with
  | none => throw (IO.userError "original constructor calls program certification rejected")
  | some certificate =>
      if rows : certificate.table.rows.all (fun row =>
          [observed.makeRow.row, observed.readRow.row].any (fun expected => row == expected)) = true then
        pure ⟨certificate, accepted, by
          intro row member
          obtain ⟨expected, present, same⟩ := List.any_eq_true.mp (List.all_eq_true.mp rows row member)
          exact (eq_of_beq same).symm ▸ present⟩
      else throw (IO.userError "actual direct table contains an unselected ordinary row")

theorem ObservedProgramCertificate.aligned {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) (inventory : OrdinaryInventory fixture observed) :
    CallableIndexedOwnedPreparedNamedSyntaxAdmission.TableAligned
      [inventory.makeInput, inventory.readInput] admission.certificate.table.rows := by
  intro row member
  have present := admission.rows row member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl
  · exact ⟨inventory.makeInput, by simp, inventory.makeRow⟩
  · exact ⟨inventory.readInput, by simp, inventory.readRow⟩

/-- The primary production entry point constructs its own complete eligible
ordinary catalog and closes table alignment without the selected subset. -/
theorem ObservedProgramCertificate.automatic_catalog {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) (receiver : ObservedReceiver fixture observed) :
    ∃ catalog : CallableIndexedOwnedPreparedOrdinaryCatalogReceipts.Catalog fixture.recipe.compiled,
      Nonempty (CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
        (headers catalog.rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        receiver.completion) := by
  exact admission.certificate.issue_without_methods fixture.source_wellFormed fixture.recipePrepared receiver.issued
    receiver.registry observed.makeRow.entryMember (by rw [fixture.sameProgram]; exact fixture.checked)
    (by rw [fixture.sameProgram]; exact fixture.methods)

/-- This proof is exercised by the same runtime-produced certificate used by
the nine-operation regression; catalog construction is kept inside the proof. -/
theorem ObservedProgramCertificate.automatic_catalog_initial {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed,
      ∃ catalog : CallableIndexedOwnedPreparedOrdinaryCatalogReceipts.Catalog fixture.recipe.compiled,
        Nonempty (CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
          (headers catalog.rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
          receiver.completion) := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  exact ⟨receiver, admission.automatic_catalog receiver⟩

end Tests.SourceCoreConstructorCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreConstructorCallsReadSupport
/-! The observed constructor body supplies its named support from the actual
recursive expression tree, including an indirect call in the first payload.
No Source execution or payload representation is an input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreConstructorCalls
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

private theorem read_expressions {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) {id : ExpressionId} {node : ExpressionNode}
    (found : observed.readRow.row.function.typedBody.lookupExpression? id = some node) :
    node = observed.readShape.argumentRead.node ∨ node = observed.readShape.factoryRead.node ∨ node = observed.readShape.call.node ∨ node = observed.readShape.priorRead.node ∨ node = observed.readShape.retainedFactoryRead.node ∨ node = observed.readShape.convertRead.node ∨ node = observed.readShape.expression.node := by
  have present := (lookupExpression?_sound found).1
  rw [observed.readNodes] at present
  simpa only [ReadShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present

theorem ActualHeader.read_metadata {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.readRow.row)
    (named : CallableIndexedNamedGeneration.Named) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.MetadataFor
      fixture.recipe.compiled.indexed named actual.header.function.source := by
  constructor
  · intro id _ node found
    rw [actual.source] at found
    rcases read_expressions observed found with same | same | same | same | same | same | same
    all_goals subst node
    · exact observed.readShape.argumentRead.requirements
    · exact observed.readShape.factoryRead.requirements
    · exact observed.readShape.call.requirements
    · exact observed.readShape.priorRead.requirements
    · exact observed.readShape.retainedFactoryRead.requirements
    · exact observed.readShape.convertRead.requirements
    · exact observed.readShape.expression.requirements
  · intro id _ node found
    rw [actual.source] at found
    rcases read_expressions observed found with same | same | same | same | same | same | same
    all_goals subst node
    · exact observed.readShape.argumentRead.coercions
    · exact observed.readShape.factoryRead.coercions
    · exact observed.readShape.call.coercions
    · exact observed.readShape.priorRead.coercions
    · exact observed.readShape.retainedFactoryRead.coercions
    · exact observed.readShape.convertRead.coercions
    · exact observed.readShape.expression.coercions
  · intro id _
    simp only [observed.noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    rw [actual.source] at found
    rcases read_expressions observed found with same | same | same | same | same | same | same
    all_goals subst node
    · rw [observed.readShape.argumentRead.form] at form
      cases form
    · rw [observed.readShape.factoryRead.form] at form
      cases form
    · rw [observed.readShape.callForm] at form
      have same := (ExpressionForm.call.inj form).2.2
      cases same
      rw [observed.readShape.applicationEq]
    · rw [observed.readShape.priorRead.form] at form
      cases form
    · rw [observed.readShape.retainedFactoryRead.form] at form
      cases form
    · rw [observed.readShape.convertRead.form] at form
      cases form
    · rw [observed.readShape.expressionForm] at form
      cases form
  · intro id _ node _found name binder _form
    simp only [observed.noLocals, List.any_nil]

theorem ActualHeader.read_syntax {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.readRow.row) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax
      actual.header.function.source observed.readShape.expression.node.id := by
  rw [actual.source]
  apply CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax.constructor
    observed.readShape.expression.found observed.readShape.expressionForm
  · rw [observed.readShape.instantiationEq]
    intro parameter type member
    cases member
  · intro child member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact .call observed.readShape.call.found observed.readShape.callForm
        (.leaf (.read observed.readShape.factoryRead.found observed.readShape.factoryRead.form))
        (by intro id member; cases List.mem_singleton.mp member
            exact .leaf (.read observed.readShape.argumentRead.found observed.readShape.argumentRead.form))
    · exact .leaf (.read observed.readShape.priorRead.found observed.readShape.priorRead.form)
    · exact .leaf (.read observed.readShape.retainedFactoryRead.found observed.readShape.retainedFactoryRead.form)
    · exact .leaf (.read observed.readShape.convertRead.found observed.readShape.convertRead.form)

/-- All finite metadata, original typing and selected scope premises of the
compiler producer are derived from this concrete checked/compiled fixture. -/
theorem ActualHeader.read_support_at {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.readRow.row)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (expression : terminal.expression = observed.readShape.expression.node.id)
    (point : terminal.certificate = CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
      (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty (CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.NamedSupport
      actual.header (RecursiveNamedPreparedStageScopes.registry stagePrepared) terminal
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  exact CallableIndexedOwnedPreparedStagedNamedRecursiveTerminalSupport.of_actual
    terminal diagnostic receiver fixture.source_wellFormed (ActualHeader.read_metadata observed actual terminal.prepared.named)
    (by rw [expression]; exact ActualHeader.read_syntax observed actual) stagePrepared point

/-- The actual terminal lowering supplies its own Point certificate and
preparation packet before the concrete support producer is invoked. -/
theorem ActualHeader.read_support {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.readRow.row)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    ∃ terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header,
      terminal.expression = observed.readShape.expression.node.id ∧
      Nonempty (CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.NamedSupport
        actual.header (RecursiveNamedPreparedStageScopes.registry stagePrepared) terminal
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  obtain ⟨terminal, diagnostic, expression, point⟩ := actual.terminal observed.readShape.expression.node.id
    observed.readShape.statement observed.readShape.roots observed.readShape.statementFound observed.readShape.statementForm
  exact ⟨terminal, expression, ActualHeader.read_support_at observed actual terminal diagnostic expression point receiver stagePrepared⟩

end Tests.SourceCoreConstructorCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreConstructorCallsRuntime
/-! Actual public calls reuse distinct closure exports through the returned
sessions. Every step retains its original startup and run receipts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreConstructorCalls
open Solcore Frontend SourceInference SourceSemantics

def secondSeed : Core.Word := Core.Word.ofNatModulo 20
def interveningSeed : Core.Word := Core.Word.ofNatModulo 30

structure ObservedCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) where
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start key arguments runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion artifact
  executed : session.RunAt key arguments runOptions (.ok (.succeeded completion))

def observeCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (ObservedCall session key arguments) := do
  match started : session.start key arguments runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint =>
    let executed ← session.runWithReceipt key arguments runOptions
    match result : executed.val with
    | .error error => throw (IO.userError (reprStr error))
    | .ok (.failed _ _) => throw (IO.userError "captured reuse public call failed")
    | .ok (.exportError error _) => throw (IO.userError (reprStr error))
    | .ok (.outOfFuel _) => throw (IO.userError "captured reuse public call exhausted")
    | .ok (.succeeded completion) =>
      return ⟨checkpoint, started, completion, result ▸ executed.property⟩

structure ObservedFunctionCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) extends ObservedCall session key arguments where
  handle : SourceCorePublicValues.Handle
  returned : completion.value = .function handle

def observeFunctionCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (ObservedFunctionCall session key arguments) := do
  let call ← observeCall session key arguments
  match returned : call.completion.value with
  | .function handle => return ⟨call, handle, returned⟩
  | _ => throw (IO.userError "captured reuse expected a function export")

def issuanceFuel : Nat := 1024

structure ObservedNamed {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key) where
  completion : SourceCoreExecution.Completion artifact
  issued : session.NamedIssuedAt key issuanceFuel completion
  handle : SourceCorePublicValues.Handle
  returned : completion.value = .function handle

structure ObservedInvocation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle)
    (argument : SourceCorePublicValues.Value) where
  completion : SourceCoreExecution.Completion artifact
  executed : session.InvokeAt handle argument runOptions (.ok (.succeeded completion))

def observeNamed {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key) :
    IO (ObservedNamed session key) := do
  match ← session.namedWithReceipt key issuanceFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok result =>
    match returned : result.val.value with
    | .function handle => pure ⟨result.val, result.property, handle, returned⟩
    | _ => throw (IO.userError "named issuance did not return a function")

def observeInvocation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle)
    (argument : SourceCorePublicValues.Value) : IO (ObservedInvocation session handle argument) := do
  let executed ← session.invokePackedWithReceipt handle argument runOptions
  match result : executed.val with
  | .error error => throw (IO.userError (reprStr error))
  | .ok (.failed _ _) => throw (IO.userError "direct issued call failed")
  | .ok (.exportError error _) => throw (IO.userError (reprStr error))
  | .ok (.outOfFuel _) => throw (IO.userError "direct issued call exhausted")
  | .ok (.succeeded completion) => pure ⟨completion, result ▸ executed.property⟩


structure ObservedBuiltin {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) where
  completion : SourceCoreExecution.Completion artifact
  issued : session.BuiltinIssuedAt .wordFromInteger issuanceFuel completion
  handle : SourceCorePublicValues.Handle
  returned : completion.value = .function handle

def observeBuiltin {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) : IO (ObservedBuiltin session) := do
  match ← session.builtinWithReceipt .wordFromInteger issuanceFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok result =>
    match returned : result.val.value with
    | .function handle => pure ⟨result.val, result.property, handle, returned⟩
    | _ => throw (IO.userError "builtin issuance did not return a function")


def packedArgument (factory prior convert : SourceCorePublicValues.Handle) : SourceCorePublicValues.Value :=
  .product (.function factory) (.product (.word secondSeed) (.product (.function prior) (.function convert)))

structure ObservedConstruction {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle factory prior convert : SourceCorePublicValues.Handle)
    (instantiation : DataConstructorInstantiation)
    extends ObservedInvocation session handle (packedArgument factory prior convert) where
  newOutput : SourceCorePublicValues.Handle
  priorOutput : SourceCorePublicValues.Handle
  factoryOutput : SourceCorePublicValues.Handle
  builtinOutput : SourceCorePublicValues.Handle
  returned : completion.value = .constructed instantiation
    [.function newOutput, .function priorOutput, .function factoryOutput, .function builtinOutput]
  priorSame : priorOutput = prior
  factorySame : factoryOutput = factory
  builtinSame : builtinOutput = convert
  distinct : newOutput ≠ priorOutput
  newType : newOutput.sourceType = closureType
  priorType : priorOutput.sourceType = closureType
  factoryType : factoryOutput.sourceType = makerType
  builtinType : builtinOutput.sourceType = convertType

def observeConstruction {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle factory prior convert : SourceCorePublicValues.Handle)
    (instantiation : DataConstructorInstantiation) :
    IO (ObservedConstruction session handle factory prior convert instantiation) := do
  let call ← observeInvocation session handle (packedArgument factory prior convert)
  match call.completion.value with
  | .constructed _ [.function newOutput, .function priorOutput, .function factoryOutput, .function builtinOutput] =>
    if returned : call.completion.value = .constructed instantiation
        [.function newOutput, .function priorOutput, .function factoryOutput, .function builtinOutput] then
      if priorSame : priorOutput = prior then
        if factorySame : factoryOutput = factory then
          if builtinSame : builtinOutput = convert then
            if distinct : newOutput ≠ priorOutput then
              if newType : newOutput.sourceType = closureType then
                if priorType : priorOutput.sourceType = closureType then
                  if factoryType : factoryOutput.sourceType = makerType then
                    if builtinType : builtinOutput.sourceType = convertType then
                      return ⟨call, newOutput, priorOutput, factoryOutput, builtinOutput, returned,
                        priorSame, factorySame, builtinSame, distinct, newType, priorType, factoryType, builtinType⟩
                    else throw (IO.userError "constructor builtin raw signature")
                  else throw (IO.userError "constructor factory raw signature")
                else throw (IO.userError "constructor prior raw signature")
              else throw (IO.userError "constructor new raw signature")
            else throw (IO.userError "constructor lost distinct captures")
          else throw (IO.userError "constructor changed builtin handle")
        else throw (IO.userError "constructor changed factory handle")
      else throw (IO.userError "constructor changed prior handle")
    else throw (IO.userError "constructor changed payload metadata or order")
  | _ => throw (IO.userError "constructor output expected four handles")

structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  first : ObservedPublicRun fixture observed.makeRow
  factory : ObservedNamed first.completion.session observed.makeRow.row.key
  builtin : ObservedBuiltin factory.completion.session
  named : ObservedNamed builtin.completion.session observed.readRow.row.key
  construction : ObservedConstruction named.completion.session named.handle factory.handle first.handle builtin.handle
    observed.readShape.instantiation
  newRead : ObservedInvocation construction.completion.session construction.newOutput .unit
  newValue : newRead.completion.value = .word secondSeed
  intervening : ObservedInvocation newRead.completion.session construction.factoryOutput (.word interveningSeed)
  interveningHandle : SourceCorePublicValues.Handle
  interveningReturned : intervening.completion.value = .function interveningHandle
  priorRead : ObservedInvocation intervening.completion.session construction.priorOutput .unit
  priorValue : priorRead.completion.value = .word seed
  builtinRead : ObservedInvocation priorRead.completion.session construction.builtinOutput (.integer 37)
  builtinValue : builtinRead.completion.value = .word (Core.Word.ofNatModulo 37)

def observeSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedSequence fixture observed) := do
  let first ← observePublicRun fixture observed.makeRow
  let factory ← observeNamed first.completion.session observed.makeRow.row.key
  let builtin ← observeBuiltin factory.completion.session
  let named ← observeNamed builtin.completion.session observed.readRow.row.key
  let construction ← observeConstruction named.completion.session named.handle factory.handle first.handle builtin.handle
    observed.readShape.instantiation
  let newRead ← observeInvocation construction.completion.session construction.newOutput .unit
  if newValue : newRead.completion.value = .word secondSeed then
    let intervening ← observeInvocation newRead.completion.session construction.factoryOutput (.word interveningSeed)
    match interveningReturned : intervening.completion.value with
    | .function interveningHandle =>
      let priorRead ← observeInvocation intervening.completion.session construction.priorOutput .unit
      if priorValue : priorRead.completion.value = .word seed then
        let builtinRead ← observeInvocation priorRead.completion.session construction.builtinOutput (.integer 37)
        if builtinValue : builtinRead.completion.value = .word (Core.Word.ofNatModulo 37) then
          pure ⟨first, factory, builtin, named, construction, newRead, newValue, intervening, interveningHandle,
            interveningReturned, priorRead, priorValue, builtinRead, builtinValue⟩
        else throw (IO.userError "collected builtin did not return 37")
      else throw (IO.userError "collected prior capture did not return 10")
    | _ => throw (IO.userError "collected factory did not export a closure")
  else throw (IO.userError "indirect constructor child did not capture 20")

end Tests.SourceCoreConstructorCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreConstructorCallsSupports
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreConstructorCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

structure StaticSupportPackage (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed)
    extends OrdinaryInventory fixture observed where
  program : CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
    (headers toOrdinaryInventory.rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
    completion

theorem static_supports (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (admission : ObservedProgramCertificate fixture observed)
    (makeStages : ObservedStages fixture observed.makeRow)
    (readStages : ObservedStages fixture observed.readRow)
    (receiver : ObservedReceiver fixture observed) :
    Nonempty (StaticSupportPackage fixture observed receiver.completion) := by
  obtain ⟨inventory⟩ := ordinary_inventory fixture observed makeStages readStages
  obtain ⟨program⟩ := admission.certificate.issue_for_without_methods fixture.source_wellFormed
    fixture.recipePrepared receiver.issued receiver.registry observed.makeRow.entryMember
    inventory.rows (admission.aligned inventory)
    (by rw [fixture.sameProgram]; exact fixture.checked)
    (by rw [fixture.sameProgram]; exact fixture.methods)
  exact ⟨{toOrdinaryInventory := inventory, program := program}⟩

end Tests.SourceCoreConstructorCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreConstructorCallsCommon
/-! Genuine initial diagnostics and current retained public sessions. No
independent native execution is used to construct the semantic receiver. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreConstructorCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open RecursiveNamedPublicFunctionHistory (Entry)

abbrev PublicSupports {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (receiver : ObservedReceiver fixture observed) :=
  StaticSupportPackage fixture observed receiver.completion

def PublicSupports.functions {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :=
  CallableIndexedOwnedPhysicalCellOrigins.functions (headers support.rows)
    (keys fixture.recipe.compiled) receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics) observed.profile

theorem PublicSupports.observations {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :
    CompatibleEquality.FunctionObservations fixture.recipe.compiled.compatible.checked.catalog
      support.functions (CallableIndexedLambdaValues.Identity fixture.recipe.compiled.indexed) := by
  intro metadata mapping world sourceType source native type origin
  exact CallableIndexedOwnedGeneralLambdaValues.observations _ receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
    observed.profile (registry := metadata)
    (CallableIndexedOwnedPhysicalCellOrigins.functions_include_general observed.profile origin)

abbrev RetainedState {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {publicArtifact : SourceCoreExecution.Artifact} (publicSession : SourceCoreExecution.Session publicArtifact)
    (entries : List Entry) :=
  RecursiveNamedPublicPhysicalSessionState.State support.rows support.makeHeader.header
    receiver.completion observed.profile fixture.recipe publicSession entries

abbrev SourceCall {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (arguments : List Dynamic.Value)
    (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  RecursiveNamedPublicPhysicalSessionState.SourceCall support.makeHeader.header header
    invocation before arguments outcome after

end Tests.SourceCoreConstructorCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreConstructorCallsInvocation
/-! Collected closure handles use the current metadata receiver.
Each returned state retains that receiver for the following public call. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreConstructorCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

def SourceInvocation {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (source : Dynamic.Value)
    (arguments : List Dynamic.Value) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ size, Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) size invocation
    support.makeHeader.header.function.context before source arguments outcome after

/-- Current history supplies the callee; literal input rows supply its argument.
No registry equality, arbitrary receiving table or metadata extension is assumed. -/
theorem invoke_word {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries)
    {parameter : TypeSystem.Ty}
    (entryType : entry.sourceType = .function parameter .word)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    (handleType : handle.sourceType = .function parameter .word)
    {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries
      support.makeHeader.header.function.context parameter argument packedSource)
    (call : ObservedInvocation publicSession handle argument)
    {word : Core.Word} (returned : call.completion.value = .word word)
    (invocation : Staging.Recursive.Scope) :
    ∃ (sources : List Dynamic.Value) (after : RetainedState support call.completion.session entries),
      Dynamic.ValuesPack sources packedSource ∧
      SourceInvocation support invocation state.heap entry.source sources (.value (.word word)) after.heap := by
  obtain ⟨sources, packing, _arity, next, size, trace⟩ :=
    RecursiveNamedPublicPhysicalSessionDirectScalarStep.State.invoke_scalar support.program
      fixture.recipePrepared state entry member (.word word) entryType
      (entryHandle ▸ handleType) input (by simpa only [entryHandle] using call.executed)
      returned invocation
  exact ⟨sources, next, packing, size, trace⟩


/-- Successful intervening execution retains the complete old history even
when its new result is left unselected. The actual Source value is still kept. -/
theorem invoke_success {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries) {parameter result : TypeSystem.Ty}
    (entryType : entry.sourceType = .function parameter result)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries
      support.makeHeader.header.function.context parameter argument packedSource)
    (call : ObservedInvocation publicSession handle argument)
    (invocation : Staging.Recursive.Scope) :
    ∃ (sources : List Dynamic.Value) (source : Dynamic.Value)
      (after : RetainedState support call.completion.session entries),
      Dynamic.ValuesPack sources packedSource ∧
      SourceInvocation support invocation state.heap entry.source sources (.value source) after.heap := by
  obtain ⟨sources, packing, _arity, source, next, size, trace⟩ :=
    RecursiveNamedPublicPhysicalSessionDirectSuccessStep.State.invoke_success support.program
      fixture.recipePrepared state entry member entryType input
      (by simpa only [entryHandle] using call.executed) invocation
  exact ⟨sources, source, next, packing, size, trace⟩

end Tests.SourceCoreConstructorCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreConstructorCallsSelection
/-! The original first-match receipts select the exact member of the two-row
inventory. Raw types come from checked Source signatures and the accepted
specialization, independently of execution or native type tags. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreConstructorCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicRootMeaning (RootSelection)
open RecursiveNamedPublicHistoryFrontdoor (Started)

theorem ActualHeader.key {fixture : CompiledFixture}
    {row : SourceSpecialization.SpecializedFunction} (actual : ActualHeader fixture row) :
    actual.header.named.signature.key = row.key := by
  rw [actual.aligned.named]
  exact RecursiveNamedPreparedCallEvidence.Prepared.signature_key actual.prepared

theorem ObservedProgram.keys_distinct {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) : observed.makeRow.row.key ≠ observed.readRow.row.key := by
  intro same
  have globals : observed.makeRow.global.key = observed.readRow.global.key :=
    observed.makeRow.globalKey.trans (same.trans observed.readRow.globalKey.symm)
  exact observed.distinctSlots (observed.makeRow.slot.unique observed.readRow.slot globals).2

private theorem selected_key {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {root : SourceCoreIndexedSession.Root compiled}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (selected : RootSelection (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers root header) :
    header.named.signature.key = root.key := by
  obtain ⟨_, entry, _, shape, found⟩ := selected
  obtain ⟨named, index, first, namedKey, rootKey, _⟩ := shape
  obtain ⟨namedEq, _⟩ := Prod.mk.inj (Option.some.inj (found.symm.trans first))
  rw [namedEq]
  exact namedKey.trans rootKey.symm

theorem selected_make_root {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (readHeader : ActualHeader fixture observed.readRow.row)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (selected : RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [makeHeader.header, readHeader.header] root header)
    (key : root.key = observed.makeRow.row.key) : header = makeHeader.header := by
  rcases List.mem_cons.mp selected.member with same | rest
  · exact same
  · have same := List.mem_singleton.mp rest
    have headerKey := (selected_key selected).trans key
    rw [same, readHeader.key] at headerKey
    exact False.elim (observed.keys_distinct headerKey.symm)

theorem selected_read_root {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (readHeader : ActualHeader fixture observed.readRow.row)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (selected : RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [makeHeader.header, readHeader.header] root header)
    (key : root.key = observed.readRow.row.key) : header = readHeader.header := by
  rcases List.mem_cons.mp selected.member with same | rest
  · have headerKey := (selected_key selected).trans key
    rw [same, makeHeader.key] at headerKey
    exact False.elim (observed.keys_distinct headerKey)
  · exact List.mem_singleton.mp rest

private theorem cast_key {left right : SourceCoreUnifiedCompilation.Compiled}
    (same : left = right) (root : SourceCoreIndexedSession.Root left) :
    (same ▸ root).key = root.key := by
  cases same
  rfl

private theorem started_key {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {recipe : SourceCoreIndexedSession.Recipe}
    {prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe}
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {nativeArtifact : SourceCoreIndexedSession.Artifact}
    {session : SourceCoreIndexedSession.Session nativeArtifact}
    {key : SourceCoreIndexedSession.Key} {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {world : Core.StoreTyping} {store : Core.Store}
    (request : Started headers prepared publicCheckpoint session key arguments fuel world store) :
    request.root.key = key := by
  have keyEq := of_decide_eq_true (List.find?_some
    (p := fun root : SourceCoreIndexedSession.Root recipe.compiled => decide (root.key = key))
    request.started.selected)
  exact (cast_key (SourceCoreIndexedSession.Recipe.prepare_compiled prepared).symm request.root).symm.trans keyEq

section StartedSelection
variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  (makeHeader : ActualHeader fixture observed.makeRow.row)
  (readHeader : ActualHeader fixture observed.readRow.row)
  {publicArtifact : SourceCoreExecution.Artifact}
  {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
  {nativeArtifact : SourceCoreIndexedSession.Artifact}
  {session : SourceCoreIndexedSession.Session nativeArtifact}
  {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
  {world : Core.StoreTyping} {store : Core.Store}

theorem selected_make (request : Started [makeHeader.header, readHeader.header]
    fixture.recipePrepared publicCheckpoint session observed.makeRow.row.key arguments fuel world store) :
    request.header = makeHeader.header :=
  selected_make_root makeHeader readHeader request.selected (started_key request)

theorem selected_read (request : Started [makeHeader.header, readHeader.header]
    fixture.recipePrepared publicCheckpoint session observed.readRow.row.key arguments fuel world store) :
    request.header = readHeader.header :=
  selected_read_root makeHeader readHeader request.selected (started_key request)

theorem selected_make_at
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (headerList : headers = [makeHeader.header, readHeader.header])
    (request : Started headers fixture.recipePrepared publicCheckpoint session
      observed.makeRow.row.key arguments fuel world store) : request.header = makeHeader.header := by
  subst headers
  exact selected_make makeHeader readHeader request

theorem selected_read_at
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (headerList : headers = [makeHeader.header, readHeader.header])
    (request : Started headers fixture.recipePrepared publicCheckpoint session
      observed.readRow.row.key arguments fuel world store) : request.header = readHeader.header := by
  subst headers
  exact selected_read makeHeader readHeader request
end StartedSelection

theorem StaticSupportPackage.header_list {fixture : CompiledFixture}
    {observed : ObservedProgram fixture}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (support : StaticSupportPackage fixture observed completion) :
    CallableIndexedOwnedPreparedFiniteNamedInventories.headers support.rows =
      [support.makeHeader.header, support.readHeader.header] := by
  rw [support.rowsEq]
  simp only [CallableIndexedOwnedPreparedFiniteNamedInventories.headers, support.makeEq, support.readEq]


private theorem parameter_nil (type : TypeSystem.Ty) :
    TypeSystem.ParameterSubstitution.apply [] type = type := by
  induction type <;> simp_all [TypeSystem.ParameterSubstitution.apply,
    TypeSystem.ParameterSubstitution.lookup?]

theorem ObservedRow.source_types {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    (observed : ObservedRow fixture signature)
    (signatureMember : signature ∈ fixture.recipe.compiled.sourceProgram.signatures.functions)
    (actual : ActualHeader fixture observed.row) :
    observed.row.function.typedBody.inputs.map (fun binder => binder.scheme.body) = signature.parameterTypes ∧
      observed.row.function.inferredBodyType = TypeSystem.Ty.productMany signature.returnTypes := by
  obtain ⟨request, original, generic, originalMember, genericMember, _, accepted⟩ := actual.prepared.origin
  have identities := RecursiveNamedSpecializationBodyFacts.identities accepted
  have body := RecursiveNamedSpecializationBodyFacts.body accepted
  have owner := congrArg (fun source => source.owner) body
  change observed.row.function.typedBody.owner = generic.typedBody.owner at owner
  have originalEq : original = signature :=
    eq_of_mem_of_nodup_map fixture.source_wellFormed.signatures.function_ids originalMember signatureMember
      (identities.1.trans (identities.2.1.symm.trans (owner.symm.trans observed.sourceOwner)))
  subst original
  have valid := fixture.source_wellFormed.functions_valid (FunctionDefinition.ofChecked generic)
    (List.mem_map.mpr ⟨generic, genericMember, rfl⟩)
  cases valid with
  | @intro typedSignature facts typedMember typedOwner bodyValid =>
    have same : typedSignature = signature :=
      eq_of_mem_of_nodup_map fixture.source_wellFormed.signatures.function_ids typedMember signatureMember
        (typedOwner.symm.trans identities.1.symm)
    subst typedSignature
    cases bodyValid with
    | intro _ _ _ _ _ result _ _ _ extended _ _ _ _ _ _ =>
      have inputs := Dynamic.MonoBindersExtend.bodyTypes_eq extended
      have fields := (CallableCoercionBodyProvenance.specialization_fields accepted).1
      rw [fields, observed.parameters]
      simp only [SourceSpecialization.applyCheckedFunction, SourceSpecialization.applyTypedSource,
        List.map_map, Function.comp_def, SourceSpecialization.applyBinder,
        SourceSpecialization.applyScheme, parameter_nil]
      exact ⟨inputs, result⟩

theorem ActualHeader.read_input_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.readRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [makerType, .word, closureType, convertType] := by
  have raw := (observed.readRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.head _)) actual).1
  rw [observed.readShape.inputTypes] at raw
  rw [← actual.source] at raw
  rw [actual.header.inputs] at raw
  simpa only [List.map_map, Function.comp_def] using raw

theorem ActualHeader.read_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.readRow.row) : actual.header.types = [makerType, .word, closureType, convertType] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  have raw := actual.read_input_types
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans raw

theorem ActualHeader.read_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.readRow.row) : actual.header.function.resultType = containerType fixture.dataType := by
  have result := (observed.readRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.head _)) actual).2
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same, result,
    observed.readShape.returns]
  rfl

theorem ActualHeader.make_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.makeRow.row) :
    actual.header.function.resultType = .function .unit .word := by
  have result := (observed.makeRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .head _) actual).2
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same, result,
    observed.makeShape.returns]
  rfl

end Tests.SourceCoreConstructorCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreConstructorCallsIssuance
/-! Real issuer receipts extend the retained history and authenticate exact raw
handle types. The Source heap remains the same across each issuance. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreConstructorCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers Inventory)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)

theorem read_source_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :
    support.readPacket.header.named.specialized.function.type = .function (TypeSystem.Ty.productMany [makerType, .word, closureType, convertType]) (containerType fixture.dataType) := by
  obtain ⟨facts, certified⟩ :=
    CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds.source_certificate
      support.readPacket.sourceAt fixture.source_wellFormed
  have shape := certified.callable_type
  change support.readPacket.header.named.specialized.function.type = _ at shape
  rw [← support.readPacket.sourceAt.frame.result, ← support.readEq,
    support.readHeader.read_types, support.readHeader.read_result_type] at shape
  rw [support.readEq] at shape
  exact shape

theorem ActualHeader.make_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.makeRow.row) : actual.header.types = [.word] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  have raw := (observed.makeRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .head _) actual).1
  rw [observed.makeShape.inputTypes, ← actual.source, actual.header.inputs] at raw
  simp only [List.map_map, Function.comp_def] at types raw
  exact types.symm.trans raw

theorem make_source_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :
    support.makePacket.header.named.specialized.function.type = makerType := by
  obtain ⟨facts, certified⟩ :=
    CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds.source_certificate
      support.makePacket.sourceAt fixture.source_wellFormed
  have shape := certified.callable_type
  change support.makePacket.header.named.specialized.function.type = _ at shape
  rw [← support.makePacket.sourceAt.frame.result, ← support.makeEq,
    support.makeHeader.make_types, support.makeHeader.make_result_type] at shape
  rw [support.makeEq] at shape
  exact shape

section State
variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
  {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
  {entries : List Entry}

/-- Named issuance appends the compiler-selected read global, preserving every
previous capture and the same actual heap. -/
theorem remember_named (state : RetainedState support publicSession entries)
    (call : ObservedNamed publicSession observed.readRow.row.key) :
    ∃ entry : Entry,
      entry.sourceType = .function (TypeSystem.Ty.productMany [makerType, .word, closureType, convertType]) (containerType fixture.dataType) ∧
      entry.handle = call.handle ∧ call.handle.sourceType = .function (TypeSystem.Ty.productMany [makerType, .word, closureType, convertType]) (containerType fixture.dataType) ∧
      entry.source = .global (CallableNamedReversal.global (CallableNamedMetadata.global
        support.readPacket.header.named.specialized support.readInput.prepared.available)) ∧
      ∃ next : RetainedState support call.completion.session (entries ++ [entry]), next.heap = state.heap := by
  have member : Inventory.HasRow support.readPacket support.rows := by
    rw [support.rowsEq]
    exact .tail _ (.here _)
  have issued : publicSession.NamedIssuedAt support.readPacket.header.named.signature.key issuanceFuel call.completion := by
    rw [← support.readEq, support.readHeader.key]
    exact call.issued
  obtain ⟨entry, sourceType, source, handle, handleType, next, heap⟩ :=
    RecursiveNamedPublicPhysicalSessionIssuance.State.remember_named support.program
      fixture.recipePrepared state support.readPacket member issued call.returned
  exact ⟨entry, sourceType.trans (read_source_type support), handle,
    handleType.trans (read_source_type support), source, next, heap⟩

/-- Named issuance appends the compiler-selected read global, preserving every
previous capture and the same actual heap. -/
theorem remember_maker (state : RetainedState support publicSession entries)
    (call : ObservedNamed publicSession observed.makeRow.row.key) :
    ∃ entry : Entry,
      entry.sourceType = makerType ∧
      entry.handle = call.handle ∧ call.handle.sourceType = makerType ∧
      entry.source = .global (CallableNamedReversal.global (CallableNamedMetadata.global
        support.makePacket.header.named.specialized support.makeInput.prepared.available)) ∧
      ∃ next : RetainedState support call.completion.session (entries ++ [entry]), next.heap = state.heap := by
  have member : Inventory.HasRow support.makePacket support.rows := by
    rw [support.rowsEq]
    exact .here _
  have issued : publicSession.NamedIssuedAt support.makePacket.header.named.signature.key issuanceFuel call.completion := by
    rw [← support.makeEq, support.makeHeader.key]
    exact call.issued
  obtain ⟨entry, sourceType, source, handle, handleType, next, heap⟩ :=
    RecursiveNamedPublicPhysicalSessionIssuance.State.remember_named support.program
      fixture.recipePrepared state support.makePacket member issued call.returned
  exact ⟨entry, sourceType.trans (make_source_type support), handle,
    handleType.trans (make_source_type support), source, next, heap⟩

/-- Builtin issuance appends the actual closed wordFromInteger payload. -/
theorem remember_builtin (state : RetainedState support publicSession entries)
    (call : ObservedBuiltin publicSession) :
    ∃ entry : Entry,
      entry.sourceType = .function .integer .word ∧ entry.handle = call.handle ∧
      call.handle.sourceType = .function .integer .word ∧ entry.source = .builtin ⟨.wordFromInteger⟩ ∧
      ∃ next : RetainedState support call.completion.session (entries ++ [entry]), next.heap = state.heap := by
  obtain ⟨entry, sourceType, source, handle, handleType, next, heap⟩ :=
    RecursiveNamedPublicPhysicalSessionIssuance.State.remember_builtin fixture.recipePrepared
      state .wordFromInteger call.issued call.returned
  exact ⟨entry, sourceType, handle, handleType, source, next, heap⟩

end State
end Tests.SourceCoreConstructorCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreConstructorCallsCertifiedHeaders
/-! The original physical cache slot identifies each automatic catalog Header.
The original public observations retain their complete execution receipts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreConstructorCalls.CompilerProfile
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open SelectedCompilationCertifiedPublicSession (EligibleRow Issued Initial)

variable {fixture : CompiledFixture} {signature : ProgramFunctionSignature}

theorem selected_row (row : ObservedRow fixture signature) :
    ∃ selected : EligibleRow fixture.recipe.compiled row.row.key,
      selected.named.specialized = row.row := by
  obtain ⟨prepared⟩ := fixture.prepared row.member
  obtain ⟨_signatureEq, indexEq⟩ := row.prepared_slot prepared
  refine ⟨⟨prepared.named, row.index, row.global, indexEq ▸ prepared.selected,
    row.slot, row.globalKey, ?_⟩, prepared.same⟩
  rw [prepared.same]
  refine ⟨prepared.origin, ?_, row.ordinary, row.inputsOrdinary⟩
  simp only [row.parameters, SourceSemantics.ParameterSubstitution.RangeWellFormed,
    List.not_mem_nil, false_implies, implies_true]

theorem header_of_member (row : ObservedRow fixture signature)
    {inputs : List (Input fixture.recipe.compiled)} (rows : Inventory inputs)
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (member : header ∈ headers rows)
    (specialized : header.named.specialized = row.row) :
    ∃ actual : ActualHeader fixture row.row, actual.header = header := by
  obtain ⟨input, packet, _retained, sameHeader⟩ := rows.mem_headers header member
  subst header
  have sameRow : input.row = row.row := input.prepared.same.symm.trans
    ((congrArg (·.specialized) packet.aligned.named.symm).trans specialized)
  have metadata : CallableNamedCanonicalOrder.retainedInstantiation input.row =
      CallableNamedMetadata.instantiation input.row := by
    simp [CallableNamedCanonicalOrder.retainedInstantiation, CallableNamedMetadata.instantiation,
      sameRow, row.parameters]
  let actual : ActualHeader fixture input.row := {
    prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected
    header := packet.header
    aligned := by simpa only [metadata] using packet.aligned
    diagnostic := ⟨⟨packet.selected.diagnostics, packet.selected.found, rfl⟩⟩ }
  have transported : ∀ (left right : SourceSpecialization.SpecializedFunction)
      (same : left = right) (value : ActualHeader fixture left),
      (same ▸ value : ActualHeader fixture right).header = value.header := by
    intro left right same value
    cases same
    rfl
  exact ⟨sameRow ▸ actual, transported _ _ sameRow actual⟩

def firstCall {row : ObservedRow fixture signature} (first : ObservedPublicRun fixture row) :
    SelectedCompilationPublicSessionState.FunctionCall first.session row.row.key [.word seed] runOptions :=
  ⟨⟨⟨first.checkpoint, first.started⟩, first.completion, first.executed⟩, first.handle, first.returned⟩

def functionCall {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {key : SourceCoreIndexedSession.Key} {arguments : List SourceCorePublicValues.Value}
    (call : ObservedFunctionCall session key arguments) :
    SelectedCompilationPublicSessionState.FunctionCall session key arguments runOptions :=
  ⟨⟨⟨call.checkpoint, call.started⟩, call.completion, call.executed⟩, call.handle, call.returned⟩

/-- The first successful export keeps the actual requested raw function type. -/
theorem initial_handle_type {issued : Issued fixture.recipe}
    {row : ObservedRow fixture signature} {first : ObservedPublicRun fixture row}
    (initial : Initial issued (firstCall first).toCall.toStartedCall) :
    first.handle.sourceType = initial.header.function.resultType := by
  obtain ⟨checkpoint, started, resumed⟩ := first.executed
  have same : checkpoint = first.checkpoint := Except.ok.inj (started.symm.trans first.started)
  subst checkpoint
  obtain ⟨_actual, _generation, _value, _store, _done, exported, valueEq, _typeEq, _budgetEq, _atSession⟩ :=
    resumed.indexed_succeeded initial.start.atCheckpoint
  have atRecipe : initial.start.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact fixture.recipe → artifact.RecipeAt fixture.recipe :=
      fun artifact atRecipe => by cases artifact; exact atRecipe
    exact convert _ initial.start.started.recipe_eq
  have requested := initial.start.started.original.result_type_at atRecipe initial.start.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result initial.start.selected).2
  rw [resultType] at requested
  exact exported.function_source_type requested (valueEq.symm.trans first.returned)

structure IssuedRow (issued : Issued fixture.recipe) (row : ObservedRow fixture signature) where
  input : Input fixture.recipe.compiled
  packet : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued input
  member : Inventory.HasRow packet issued.catalog.rows
  actual : ActualHeader fixture row.row
  headerEq : actual.header = packet.header

theorem issued_row (issued : Issued fixture.recipe) (row : ObservedRow fixture signature) :
    Nonempty (IssuedRow issued row) := by
  obtain ⟨selected, same⟩ := selected_row row
  obtain ⟨input, packet, member, _row, _index, named⟩ := issued.catalog.packet_at selected.cached selected.eligible
  obtain ⟨actual, headerEq⟩ := header_of_member row issued.catalog.rows (Inventory.header_member member)
    ((congrArg (·.specialized) (packet.aligned.named.trans named)).trans same)
  exact ⟨⟨input, packet, member, actual, headerEq⟩⟩

theorem IssuedRow.make_type {observed : ObservedProgram fixture} {issued : Issued fixture.recipe}
    (row : IssuedRow issued observed.makeRow) : row.packet.header.named.specialized.function.type = makerType := by
  obtain ⟨_facts, certified⟩ := CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds.source_certificate
    row.packet.sourceAt fixture.source_wellFormed
  have shape := certified.callable_type
  change row.packet.header.named.specialized.function.type = _ at shape
  rw [← row.packet.sourceAt.frame.result, ← row.headerEq, row.actual.make_types,
    row.actual.make_result_type] at shape
  rw [row.headerEq] at shape
  exact shape

theorem IssuedRow.read_type {observed : ObservedProgram fixture} {issued : Issued fixture.recipe}
    (row : IssuedRow issued observed.readRow) :
    row.packet.header.named.specialized.function.type = .function (TypeSystem.Ty.productMany [makerType, .word, closureType, convertType]) (containerType fixture.dataType) := by
  obtain ⟨_facts, certified⟩ := CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds.source_certificate
    row.packet.sourceAt fixture.source_wellFormed
  have shape := certified.callable_type
  change row.packet.header.named.specialized.function.type = _ at shape
  rw [← row.packet.sourceAt.frame.result, ← row.headerEq, row.actual.read_types,
    row.actual.read_result_type] at shape
  rw [row.headerEq] at shape
  exact shape

end Tests.SourceCoreConstructorCalls.CompilerProfile
end

section
-- leanmerge: from Solcore.Test.SourceCoreConstructorCallsCertifiedMeaning
/-! The original indexed closures are retained in one physical public session.
Each Source trace uses the actual selected Header and the reached Source heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreConstructorCalls.CompilerProfile
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicFunctionHistory (Entry)
open SelectedCompilationPublicSessionState (SourceCall)
open SelectedCompilationCertifiedPublicSession (Issued Initial)

structure Observed (fixture : CompiledFixture) where
  value : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled
  accepted : CompilerProgramStaticProfile.validateProfile fixture.recipe.compiled
    fixture.source_wellFormed = some value

def observe (fixture : CompiledFixture) : IO (Observed fixture) := do
  match accepted : CompilerProgramStaticProfile.validateProfile fixture.recipe.compiled fixture.source_wellFormed with
  | none => throw (IO.userError "original constructor compiler profile rejected")
  | some profile => pure ⟨profile, accepted⟩

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}

structure FirstMeaning (issued : Issued fixture.recipe)
    (stages : ObservedStages fixture observed.makeRow)
    (first : ObservedPublicRun fixture observed.makeRow) where
  initial : Initial issued (firstCall first).toCall.toStartedCall
  actual : ActualHeader fixture observed.makeRow.row
  headerEq : initial.header = actual.header
  entry : Entry
  entryType : entry.sourceType = closureType
  handleEq : entry.handle = first.handle
  handleType : first.handle.sourceType = closureType
  after : issued.State initial.header first.completion.session [entry]
  trace : SelectedCompilationPublicSessionState.SourceCall initial.header initial.header
    (RecursiveStageRegistry.scope stages.sidecar [] initial.header.function)
    ⟨[]⟩ [.word seed] (.value entry.source) after.heap

variable {issued : Issued fixture.recipe}
  {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List Entry}

theorem first_meaning (profile : Observed fixture)
    (stages : ObservedStages fixture observed.makeRow)
    (first : ObservedPublicRun fixture observed.makeRow) :
    ∃ issued : Issued fixture.recipe, Nonempty (FirstMeaning issued stages first) := by
  obtain ⟨row, rowEq⟩ := selected_row observed.makeRow
  obtain ⟨profiled, initial, namedEq⟩ := CertifiedPublicSession.from_profile_initial_row
    (by rw [fixture.sameProgram]; exact fixture.checked)
    (by rw [fixture.sameProgram]; exact fixture.accepted)
    fixture.issued profile.value fixture.source_wellFormed first.opened
    (firstCall first).toCall.toStartedCall first.bootstrap first.fresh first.authority
    (show first.bootstrap.ReadyAt 100000 first.session from .single first.ready) row
  let issued := profiled.toIssued
  obtain ⟨actual, actualEq⟩ := header_of_member observed.makeRow issued.catalog.rows
    initial.start.selected.member ((congrArg (·.specialized) namedEq).trans rowEq)
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context [.word seed] initial.header.types := by
    rw [← actualEq, actual.make_types]
    exact .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.word seed] [.word seed] :=
    .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  obtain ⟨entry, type, handle, after, trace⟩ := initial.reflect_function
    (call := firstCall first) (by intro value member; cases List.mem_singleton.mp member; exact .word seed)
    inputTypes inputMeanings (RecursiveStageRegistry.scope stages.sidecar [] initial.header.function)
  have raw : initial.header.function.resultType = closureType := by
    rw [← actualEq]; exact actual.make_result_type
  exact ⟨issued, ⟨⟨initial, actual, actualEq.symm, entry, type.trans raw, handle,
    (initial_handle_type initial).trans raw, after, trace⟩⟩⟩

theorem FirstMeaning.forward {stages : ObservedStages fixture observed.makeRow}
    {first : ObservedPublicRun fixture observed.makeRow} (meaning : FirstMeaning issued stages first) :
    SelectedCompilationPublicSessionInitialForward.ForwardAt issued.catalog.rows meaning.initial.header
      meaning.initial.header issued.support (firstCall first).toCall.toStartedCall meaning.entry.source meaning.after.heap := by
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      meaning.initial.header.function.context [.word seed] meaning.initial.header.types := by
    rw [meaning.headerEq, meaning.actual.make_types]
    exact .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  exact meaning.initial.forward_function
    (by intro value member; cases List.mem_singleton.mp member; exact .word seed)
    inputTypes (.cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil)
    (parameter := .unit) (resultType := .word)
    (by rw [meaning.headerEq, meaning.actual.make_result_type]; rfl) meaning.trace

structure NamedMeaning (issued : Issued fixture.recipe)
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (before : issued.State anchor session entries)
    {signature : ProgramFunctionSignature} (row : ObservedRow fixture signature)
    (call : ObservedNamed session row.row.key) where
  selected : IssuedRow issued row
  entry : Entry
  entryType : entry.sourceType = selected.packet.header.named.specialized.function.type
  source : entry.source = .global (CallableNamedReversal.global
    (CallableNamedMetadata.global selected.packet.header.named.specialized selected.input.prepared.available))
  handleEq : entry.handle = call.handle
  handleType : call.handle.sourceType = selected.packet.header.named.specialized.function.type
  after : issued.State anchor call.completion.session (entries ++ [entry])
  heapEq : after.heap = before.heap

theorem named_meaning (before : issued.State anchor session entries)
    {signature : ProgramFunctionSignature} (row : ObservedRow fixture signature)
    (call : ObservedNamed session row.row.key) :
    Nonempty (NamedMeaning issued before row call) := by
  obtain ⟨selected⟩ := issued_row issued row
  have issuance : session.NamedIssuedAt selected.packet.header.named.signature.key issuanceFuel call.completion := by
    rw [← selected.headerEq, selected.actual.key]
    exact call.issued
  obtain ⟨entry, type, source, handle, handleType, after, heap⟩ :=
    SelectedCompilationPublicSessionIssuance.State.remember_named issued.support issued.prepared
      before selected.packet selected.member issuance call.returned
  exact ⟨⟨selected, entry, type, source, handle, handleType, after, heap⟩⟩

structure BuiltinMeaning (issued : Issued fixture.recipe)
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (before : issued.State anchor session entries)
    (call : ObservedBuiltin session) where
  entry : Entry
  entryType : entry.sourceType = convertType
  source : entry.source = .builtin ⟨.wordFromInteger⟩
  handleEq : entry.handle = call.handle
  handleType : call.handle.sourceType = convertType
  after : issued.State anchor call.completion.session (entries ++ [entry])
  heapEq : after.heap = before.heap

theorem builtin_meaning (before : issued.State anchor session entries)
    (call : ObservedBuiltin session) : Nonempty (BuiltinMeaning issued before call) := by
  obtain ⟨entry, type, source, handle, handleType, after, heap⟩ :=
    SelectedCompilationPublicSessionIssuance.State.remember_builtin issued.prepared before
      .wordFromInteger call.issued call.returned
  exact ⟨⟨entry, type, source, handle, handleType, after, heap⟩⟩

end Tests.SourceCoreConstructorCalls.CompilerProfile
end

section
-- leanmerge: from Solcore.Test.SourceCoreConstructorCallsSeed
/-! Actual initialization and the first public make(10) execution establish
the first Source closure and history entry, including its captured parameter. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreConstructorCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicFunctionHistory (Entry)

def ObservedPublicRun.as_function_call {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (first : ObservedPublicRun fixture observed.makeRow) :
    RecursiveNamedPublicPhysicalSessionState.FunctionCall first.session observed.makeRow.row.key [.word seed] runOptions :=
  ⟨⟨⟨first.checkpoint, first.started⟩, first.completion, first.executed⟩, first.handle, first.returned⟩

theorem ObservedPublicRun.initial_start {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (first : ObservedPublicRun fixture observed.makeRow) :
    Nonempty (RecursiveNamedPublicPhysicalSessionInitial.Started support.rows fixture.recipePrepared
      support.makeHeader.header first.as_function_call.toCall.toStartedCall) := by
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ :=
    fixture.actual_start first.opened first.started
  obtain ⟨selectedHeader, selected⟩ := started.selection prepared support.complete
  have selectedEq : selectedHeader = support.makeHeader.header := by
    apply selected_make_root (fixture := fixture) (observed := observed)
      support.makeHeader support.readHeader (root := root) (header := selectedHeader)
    · exact support.header_list ▸ selected
    · exact of_decide_eq_true (List.find?_some (p := fun candidate : SourceCoreIndexedSession.Root fixture.recipe.compiled =>
        decide (candidate.key = observed.makeRow.row.key)) started.selected)
  subst selectedHeader
  exact ⟨{
    publicCompiled := fixture.facadeCompiled
    artifact := artifact, nativeSession := session, checkpoint := checkpoint, root := root
    world := world, store := store, native := native, encodedValues := encodedValues
    opened := opened, atSession := sessionAt, atCheckpoint := checkpointAt
    started := started, selected := selected, bootstrap := first.bootstrap
    bootstrapFuel := 100000, fresh := first.fresh, authority := first.authority
    ready := .single first.ready }⟩

theorem first_meaning_typed_handle {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    (extra : ObservedMake fixture observed)
    (support : PublicSupports receiver)
    (makeStages : ObservedStages fixture observed.makeRow)
    (first : ObservedPublicRun fixture observed.makeRow) :
    ∃ entry : Entry,
      entry.sourceType = .function .unit .word ∧ entry.handle = first.handle ∧
      first.handle.sourceType = .function .unit .word ∧
      ∃ state : RetainedState support first.completion.session [entry],
        SourceCall support support.makeHeader.header
          (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
          ⟨[]⟩ [.word seed] (.value entry.source) state.heap := by
  obtain ⟨start⟩ := first.initial_start support
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      support.makeHeader.header.function.context [.word seed] support.makeHeader.header.types := by
    have bindingTypes : support.makeHeader.header.types =
        support.makeHeader.header.bindings.map (fun binding => binding.1.scheme.body) := by
      have bodyTypes := Dynamic.MonoBindersExtend.bodyTypes_eq support.makeHeader.header.extended
      rw [support.makeHeader.header.parameters] at bodyTypes
      simpa only [List.map_map, Function.comp_def] using bodyTypes.symm
    rw [bindingTypes, support.makeHeader.make_input_types extra]
    exact .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.word seed] [.word seed] :=
    .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  obtain ⟨entry, type, handle, state, trace⟩ :=
    RecursiveNamedPublicPhysicalSessionInitial.first_function support.rows fixture.recipePrepared
      support.makeHeader.header support.makeHeader.header support.program support.distinct first.as_function_call start
      (by intro value member; cases List.mem_singleton.mp member; exact .word seed)
      inputTypes inputMeanings support.makeDescriptor
      (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
  obtain ⟨checkpoint, started, resumed⟩ := first.executed
  have same : checkpoint = first.checkpoint := Except.ok.inj (started.symm.trans first.started)
  subst checkpoint
  obtain ⟨actual, _generation, _value, _store, _done, exported, valueEq, _typeEq, _budgetEq, _atSession⟩ :=
    resumed.indexed_succeeded start.atCheckpoint
  have atRecipe : start.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact fixture.recipe → artifact.RecipeAt fixture.recipe :=
      fun artifact atRecipe => by cases artifact; exact atRecipe
    exact convert _ start.started.recipe_eq
  have requested := start.started.original.result_type_at atRecipe start.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result start.selected).2
  rw [resultType, support.makeHeader.make_result_type] at requested
  have handleType := exported.function_source_type requested (valueEq.symm.trans first.returned)
  exact ⟨entry, type.trans support.makeHeader.make_result_type, handle, handleType, state, trace⟩

/-- The original factory theorem remains available when the public handle's
raw type is not needed by the caller. -/
theorem first_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    (extra : ObservedMake fixture observed)
    (support : PublicSupports receiver)
    (makeStages : ObservedStages fixture observed.makeRow)
    (first : ObservedPublicRun fixture observed.makeRow) :
    ∃ entry : Entry,
      entry.sourceType = .function .unit .word ∧ entry.handle = first.handle ∧
      ∃ state : RetainedState support first.completion.session [entry],
        SourceCall support support.makeHeader.header
          (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
          ⟨[]⟩ [.word seed] (.value entry.source) state.heap := by
  obtain ⟨entry, sourceType, handle, _handleType, state, trace⟩ :=
    first_meaning_typed_handle extra support makeStages first
  exact ⟨entry, sourceType, handle, state, trace⟩

end Tests.SourceCoreConstructorCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreConstructorCallsSelectionMeaning
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreConstructorCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)
open RecursiveNamedPublicNestedOutputSelections

def outputMetadata {fixture : CompiledFixture} (observed : ObservedProgram fixture) : DataConstructorInstantiation :=
  ⟨observed.readShape.constructor.id, [], payloadTypes, containerType fixture.dataType⟩

def outputValue {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (first prior factory convert : SourceCorePublicValues.Handle) : SourceCorePublicValues.Value :=
  .constructed (outputMetadata observed) [.function first, .function prior, .function factory, .function convert]

def outputSelection {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (first prior factory convert : SourceCorePublicValues.Handle) :
    Selection (containerType fixture.dataType) (outputValue observed first prior factory convert) :=
  .constructed (.cons .function (.cons .function (.cons .function (.cons .function .nil))))

structure Collected {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (source : Dynamic.Value) (first prior factory convert : SourceCorePublicValues.Handle)
    (entries : List Entry) where
  newEntry : Entry
  priorEntry : Entry
  factoryEntry : Entry
  builtinEntry : Entry
  ordered : entries = [newEntry, priorEntry, factoryEntry, builtinEntry]
  newType : newEntry.sourceType = closureType
  priorType : priorEntry.sourceType = closureType
  factoryType : factoryEntry.sourceType = makerType
  builtinType : builtinEntry.sourceType = convertType
  newHandle : newEntry.handle = first
  priorHandle : priorEntry.handle = prior
  factoryHandle : factoryEntry.handle = factory
  builtinHandle : builtinEntry.handle = convert
  sourceValue : source = .constructed (outputMetadata observed)
    [newEntry.source, priorEntry.source, factoryEntry.source, builtinEntry.source]

theorem selected_uncast {checked : SourceCoreCompatibleCatalog.Checked}
    {artifact : SourceCoreIndexedSession.Artifact} {session : SourceCoreIndexedSession.Session artifact}
    {type : TypeSystem.Ty} {first second : SourceCorePublicValues.Value} (same : first = second)
    {selection : Selection type first} {source : Dynamic.Value} {native : Core.Value}
    {nativeType : Core.Ty} {fuel : Nat} {entries : List Entry}
    (selected : Selected checked session (same ▸ selection : Selection type second)
      source native nativeType fuel entries) :
    Selected checked session selection source native nativeType fuel entries := by
  cases same
  exact selected

theorem selected_entries {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    {checked : SourceCoreCompatibleCatalog.Checked}
    {artifact : SourceCoreIndexedSession.Artifact} {session : SourceCoreIndexedSession.Session artifact}
    {source : Dynamic.Value} {first prior factory convert : SourceCorePublicValues.Handle}
    {native : Core.Value} {type : Core.Ty} {fuel : Nat} {entries : List Entry}
    (selected : Selected checked session (outputSelection observed first prior factory convert)
      source native type fuel entries) :
    Nonempty (Collected observed source first prior factory convert entries) := by
  cases selected with
  | constructed projection children =>
    cases children with
    | more first tail =>
      cases first
      cases tail with
      | more prior tail =>
        cases prior
        cases tail with
        | more factory tail =>
          cases factory
          cases tail with
          | one builtin =>
            cases builtin
            exact ⟨⟨_, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

end Tests.SourceCoreConstructorCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreConstructorCallsCollection
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreConstructorCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

abbrev packedType : TypeSystem.Ty := TypeSystem.Ty.productMany [makerType, .word, closureType, convertType]
def packedSource (factory prior convert : Dynamic.Value) : Dynamic.Value :=
  .product factory (.product (.word secondSeed) (.product prior convert))

theorem construction_input {entries : List Entry} {context : SourceSemantics.Context}
    (factory prior convert : Entry) (factoryMember : factory ∈ entries)
    (priorMember : prior ∈ entries) (convertMember : convert ∈ entries)
    (factoryType : factory.sourceType = makerType) (priorType : prior.sourceType = closureType)
    (convertTypeEq : convert.sourceType = convertType)
    {f p c : SourceCorePublicValues.Handle} (factoryHandle : factory.handle = f)
    (priorHandle : prior.handle = p) (convertHandle : convert.handle = c) :
    RecursiveNamedPublicFunctionHistoryInputs.Input entries context packedType
      (packedArgument f p c) (packedSource factory.source prior.source convert.source) := by
  have factoryInput := RecursiveNamedPublicFunctionHistoryInputs.Input.retained (context := context) factory factoryMember
  have priorInput := RecursiveNamedPublicFunctionHistoryInputs.Input.retained (context := context) prior priorMember
  have convertInput := RecursiveNamedPublicFunctionHistoryInputs.Input.retained (context := context) convert convertMember
  rw [factoryType, factoryHandle] at factoryInput
  rw [priorType, priorHandle] at priorInput
  rw [convertTypeEq, convertHandle] at convertInput
  have wordInput : RecursiveNamedPublicFunctionHistoryInputs.Input entries context
      .word (.word secondSeed) (.word secondSeed) :=
    .data ⟨.word secondSeed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word secondSeed⟩
      ⟨.word secondSeed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word secondSeed⟩
  exact .product factoryInput (.product wordInput (.product priorInput convertInput))

def SourceConstruction {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap)
    (callee factory prior convert source : Dynamic.Value) (after : Dynamic.Heap) : Prop :=
  ∃ sources size, Dynamic.ValuesPack sources (packedSource factory prior convert) ∧
    Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) size invocation
      support.makeHeader.header.function.context before callee sources (.value source) after

theorem collect {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (pack factory prior convert : Entry) (packMember : pack ∈ entries) (factoryMember : factory ∈ entries)
    (priorMember : prior ∈ entries) (convertMember : convert ∈ entries)
    (packType : pack.sourceType = .function packedType (containerType fixture.dataType))
    (factoryType : factory.sourceType = makerType) (priorType : prior.sourceType = closureType)
    (convertTypeEq : convert.sourceType = convertType)
    {handle f p c : SourceCorePublicValues.Handle}
    (packHandle : pack.handle = handle) (factoryHandle : factory.handle = f)
    (priorHandle : prior.handle = p) (convertHandle : convert.handle = c)
    (call : ObservedConstruction publicSession handle f p c observed.readShape.instantiation)
    (invocation : Staging.Recursive.Scope) :
    ∃ (source : Dynamic.Value) (added : List Entry) (_collected : Collected observed source call.newOutput call.priorOutput call.factoryOutput call.builtinOutput added)
      (next : RetainedState support call.completion.session (entries ++ added)),
      SourceConstruction support invocation state.heap pack.source factory.source prior.source convert.source source next.heap := by
  have input := construction_input (context := support.makeHeader.header.function.context)
    factory prior convert factoryMember priorMember convertMember factoryType priorType convertTypeEq
    factoryHandle priorHandle convertHandle
  have returned : call.completion.value = outputValue observed call.newOutput call.priorOutput call.factoryOutput call.builtinOutput := by
    simpa only [observed.readShape.instantiationEq, outputValue, outputMetadata] using call.returned
  obtain ⟨sources, packing, _arity, source, added, next, sourceSize, trace, _handles, selected⟩ :=
    RecursiveNamedPublicPhysicalSessionDirectOutputCollection.State.collect support.program
      fixture.recipePrepared state pack packMember packType input
      (by simpa only [packHandle] using call.executed)
      (returned.symm ▸ outputSelection observed call.newOutput call.priorOutput call.factoryOutput call.builtinOutput)
      invocation
  obtain ⟨_artifact, _actual, _native, _type, _atCompletion, selected⟩ := selected
  obtain ⟨collected⟩ := selected_entries observed (selected_uncast returned.symm selected)
  exact ⟨source, added, collected, next, sources, sourceSize, packing, trace⟩

end Tests.SourceCoreConstructorCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreConstructorCallsCertifiedCalls
/-! The complete automatic catalog follows the original packed constructor
call, its ordered selected handles, and every subsequent retained invocation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreConstructorCalls.CompilerProfile
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicFunctionHistory (Entry)
open SelectedCompilationCertifiedPublicSession (Issued)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  {issued : Issued fixture.recipe}
  {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List Entry}

structure ConstructionMeaning (issued : Issued fixture.recipe)
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (before : issued.State anchor session entries)
    (pack factory prior convert : Entry)
    {handle f p c : SourceCorePublicValues.Handle}
    (call : ObservedConstruction session handle f p c observed.readShape.instantiation)
    (scope : Staging.Recursive.Scope) where
  member : pack ∈ entries
  packType : pack.sourceType = .function packedType (containerType fixture.dataType)
  handleEq : pack.handle = handle
  input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context packedType
    (packedArgument f p c) (packedSource factory.source prior.source convert.source)
  arguments : List Dynamic.Value
  packing : Dynamic.ValuesPack arguments (packedSource factory.source prior.source convert.source)
  arity : RecursivePublicCallableArity.Arity (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    pack.source arguments.length
  source : Dynamic.Value
  added : List Entry
  collected : Collected observed source call.newOutput call.priorOutput call.factoryOutput call.builtinOutput added
  after : issued.State anchor call.completion.session (entries ++ added)
  size : Nat
  trace : Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    (CallableIndexedOwnedPreparedPhysicalProgramSupport.stages fixture.recipe.compiled)
    size scope anchor.function.context before.heap pack.source arguments (.value source) after.heap

theorem construction_meaning (before : issued.State anchor session entries)
    (pack factory prior convert : Entry) (packMember : pack ∈ entries) (factoryMember : factory ∈ entries)
    (priorMember : prior ∈ entries) (convertMember : convert ∈ entries)
    (packType : pack.sourceType = .function packedType (containerType fixture.dataType))
    (factoryType : factory.sourceType = makerType) (priorType : prior.sourceType = closureType)
    (convertTypeEq : convert.sourceType = convertType)
    {handle f p c : SourceCorePublicValues.Handle}
    (packHandle : pack.handle = handle) (factoryHandle : factory.handle = f)
    (priorHandle : prior.handle = p) (convertHandle : convert.handle = c)
    (call : ObservedConstruction session handle f p c observed.readShape.instantiation)
    (scope : Staging.Recursive.Scope) :
    Nonempty (ConstructionMeaning issued before pack factory prior convert call scope) := by
  have input := construction_input (context := anchor.function.context)
    factory prior convert factoryMember priorMember convertMember factoryType priorType convertTypeEq
    factoryHandle priorHandle convertHandle
  have returned : call.completion.value = outputValue observed call.newOutput call.priorOutput call.factoryOutput call.builtinOutput := by
    simpa only [observed.readShape.instantiationEq, outputValue, outputMetadata] using call.returned
  obtain ⟨arguments, packing, arity, source, added, after, size, trace, _handles, selected⟩ :=
    SelectedCompilationPublicSessionDirectOutputCollection.State.collect issued.support issued.prepared
      before pack packMember packType input (by simpa only [packHandle] using call.executed)
      (returned.symm ▸ outputSelection observed call.newOutput call.priorOutput call.factoryOutput call.builtinOutput) scope
  obtain ⟨_artifact, _actual, _native, _type, _atCompletion, selected⟩ := selected
  obtain ⟨collected⟩ := selected_entries observed (selected_uncast returned.symm selected)
  exact ⟨⟨packMember, packType, packHandle, input, arguments, packing, arity,
    source, added, collected, after, size, trace⟩⟩

structure WordMeaning (issued : Issued fixture.recipe)
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (before : issued.State anchor session entries)
    (entry : Entry) (parameter : TypeSystem.Ty)
    {handle : SourceCorePublicValues.Handle} {argument : SourceCorePublicValues.Value}
    (packed : Dynamic.Value) (call : ObservedInvocation session handle argument)
    (word : Core.Word) (scope : Staging.Recursive.Scope) where
  member : entry ∈ entries
  entryType : entry.sourceType = .function parameter .word
  handleEq : entry.handle = handle
  input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context parameter argument packed
  arguments : List Dynamic.Value
  packing : Dynamic.ValuesPack arguments packed
  arity : RecursivePublicCallableArity.Arity (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    entry.source arguments.length
  after : issued.State anchor call.completion.session entries
  size : Nat
  trace : Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    (CallableIndexedOwnedPreparedPhysicalProgramSupport.stages fixture.recipe.compiled)
    size scope anchor.function.context before.heap entry.source arguments (.value (.word word)) after.heap

theorem word_meaning (before : issued.State anchor session entries)
    (entry : Entry) (member : entry ∈ entries) {parameter : TypeSystem.Ty}
    (entryType : entry.sourceType = .function parameter .word)
    {handle : SourceCorePublicValues.Handle} (handleEq : entry.handle = handle)
    (handleType : handle.sourceType = .function parameter .word)
    {argument : SourceCorePublicValues.Value} {packed : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context parameter argument packed)
    (call : ObservedInvocation session handle argument)
    {word : Core.Word} (returned : call.completion.value = .word word) (scope : Staging.Recursive.Scope) :
    Nonempty (WordMeaning issued before entry parameter packed call word scope) := by
  obtain ⟨arguments, packing, arity, after, size, trace⟩ :=
    SelectedCompilationPublicSessionDirectScalarStep.State.invoke_scalar issued.support issued.prepared
      before entry member (.word word) entryType (handleEq ▸ handleType) input
      (by simpa only [handleEq] using call.executed) returned scope
  exact ⟨⟨member, entryType, handleEq, input, arguments, packing, arity, after, size, trace⟩⟩

structure SuccessMeaning (issued : Issued fixture.recipe)
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (before : issued.State anchor session entries)
    (entry : Entry) (parameter result : TypeSystem.Ty)
    {handle : SourceCorePublicValues.Handle} {argument : SourceCorePublicValues.Value}
    (packed : Dynamic.Value) (call : ObservedInvocation session handle argument)
    (scope : Staging.Recursive.Scope) where
  member : entry ∈ entries
  entryType : entry.sourceType = .function parameter result
  handleEq : entry.handle = handle
  input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context parameter argument packed
  arguments : List Dynamic.Value
  packing : Dynamic.ValuesPack arguments packed
  arity : RecursivePublicCallableArity.Arity (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    entry.source arguments.length
  source : Dynamic.Value
  after : issued.State anchor call.completion.session entries
  size : Nat
  trace : Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    (CallableIndexedOwnedPreparedPhysicalProgramSupport.stages fixture.recipe.compiled)
    size scope anchor.function.context before.heap entry.source arguments (.value source) after.heap

theorem success_meaning (before : issued.State anchor session entries)
    (entry : Entry) (member : entry ∈ entries) {parameter result : TypeSystem.Ty}
    (entryType : entry.sourceType = .function parameter result)
    {handle : SourceCorePublicValues.Handle} (handleEq : entry.handle = handle)
    {argument : SourceCorePublicValues.Value} {packed : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context parameter argument packed)
    (call : ObservedInvocation session handle argument) (scope : Staging.Recursive.Scope) :
    Nonempty (SuccessMeaning issued before entry parameter result packed call scope) := by
  obtain ⟨arguments, packing, arity, source, after, size, trace⟩ :=
    SelectedCompilationPublicSessionDirectSuccessStep.State.invoke_success issued.support issued.prepared
      before entry member entryType input (by simpa only [handleEq] using call.executed) scope
  exact ⟨⟨member, entryType, handleEq, input, arguments, packing, arity, source, after, size, trace⟩⟩

theorem ConstructionMeaning.forward
    {before : issued.State anchor session entries} {pack factory prior convert : Entry}
    {handle f p c : SourceCorePublicValues.Handle}
    {call : ObservedConstruction session handle f p c observed.readShape.instantiation}
    {scope : Staging.Recursive.Scope}
    (meaning : ConstructionMeaning issued before pack factory prior convert call scope)
    (ready : session.ExportsReady) :
    ∃ checkpoint, session.startHandlePacked handle (packedArgument f p c) runOptions.inputValidationFuel = .ok checkpoint ∧
      SelectedCompilationPublicSessionDirectOutputForward.ForwardAt issued.catalog.rows anchor
        issued.initial issued.support.profile fixture.recipe entries (containerType fixture.dataType)
        checkpoint meaning.source meaning.after.heap := by
  obtain ⟨checkpoint, accepted, _resumed⟩ := call.executed
  refine ⟨checkpoint, accepted, ?_⟩
  exact SelectedCompilationPublicSessionDirectOutputForward.forward_call issued.support issued.prepared
    before pack meaning.member meaning.packType meaning.input
    (by simpa only [meaning.handleEq] using accepted) ready meaning.packing meaning.trace

theorem WordMeaning.forward {before : issued.State anchor session entries} {entry : Entry}
    {parameter : TypeSystem.Ty} {handle : SourceCorePublicValues.Handle} {argument : SourceCorePublicValues.Value}
    {packed : Dynamic.Value} {call : ObservedInvocation session handle argument}
    {word : Core.Word} {scope : Staging.Recursive.Scope}
    (meaning : WordMeaning issued before entry parameter packed call word scope) :
    ∃ checkpoint, session.startHandlePacked handle argument runOptions.inputValidationFuel = .ok checkpoint ∧
      SelectedCompilationPublicSessionDirectWordForward.ForwardAt issued.catalog.rows anchor
        issued.initial issued.support.profile fixture.recipe entries word checkpoint meaning.after.heap := by
  obtain ⟨checkpoint, accepted, _resumed⟩ := call.executed
  refine ⟨checkpoint, accepted, ?_⟩
  exact SelectedCompilationPublicSessionDirectWordForward.forward_call issued.support issued.prepared
    before entry meaning.member word meaning.entryType meaning.input
    (by simpa only [meaning.handleEq] using accepted) meaning.packing meaning.trace

theorem SuccessMeaning.forward {before : issued.State anchor session entries} {entry : Entry}
    {parameter result : TypeSystem.Ty} {handle : SourceCorePublicValues.Handle} {argument : SourceCorePublicValues.Value}
    {packed : Dynamic.Value} {call : ObservedInvocation session handle argument} {scope : Staging.Recursive.Scope}
    (meaning : SuccessMeaning issued before entry parameter result packed call scope)
    (ready : session.ExportsReady) :
    ∃ checkpoint, session.startHandlePacked handle argument runOptions.inputValidationFuel = .ok checkpoint ∧
      SelectedCompilationPublicSessionDirectOutputForward.ForwardAt issued.catalog.rows anchor
        issued.initial issued.support.profile fixture.recipe entries result checkpoint meaning.source meaning.after.heap := by
  obtain ⟨checkpoint, accepted, _resumed⟩ := call.executed
  refine ⟨checkpoint, accepted, ?_⟩
  exact SelectedCompilationPublicSessionDirectOutputForward.forward_call issued.support issued.prepared
    before entry meaning.member meaning.entryType meaning.input
    (by simpa only [meaning.handleEq] using accepted) ready meaning.packing meaning.trace

end Tests.SourceCoreConstructorCalls.CompilerProfile
end

section
-- leanmerge: from Solcore.Test.SourceCoreConstructorCallsCompilerProfile
/-! One checked compiler profile supplies the complete catalog and physical
support for the original nine constructor operations and their nested exports. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 6000000
namespace Tests.SourceCoreConstructorCalls.CompilerProfile
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicFunctionHistory (Entry)
open SelectedCompilationCertifiedPublicSession (Issued)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}

structure SequenceMeaning (issued : Issued fixture.recipe)
    (stages : ObservedStages fixture observed.makeRow) (sequence : ObservedSequence fixture observed) where
  first : FirstMeaning issued stages sequence.first
  factory : NamedMeaning issued first.after observed.makeRow sequence.factory
  builtin : BuiltinMeaning issued factory.after sequence.builtin
  named : NamedMeaning issued builtin.after observed.readRow sequence.named
  construction : ConstructionMeaning issued named.after named.entry factory.entry first.entry builtin.entry sequence.construction
    (RecursiveStageRegistry.scope stages.sidecar [] first.initial.header.function)
  newRead : WordMeaning issued construction.after construction.collected.newEntry .unit .unit sequence.newRead secondSeed
    (RecursiveStageRegistry.scope stages.sidecar [] first.initial.header.function)
  intervening : SuccessMeaning issued newRead.after construction.collected.factoryEntry .word closureType
    (.word interveningSeed) sequence.intervening
    (RecursiveStageRegistry.scope stages.sidecar [] first.initial.header.function)
  priorRead : WordMeaning issued intervening.after construction.collected.priorEntry .unit .unit sequence.priorRead seed
    (RecursiveStageRegistry.scope stages.sidecar [] first.initial.header.function)
  builtinRead : WordMeaning issued priorRead.after construction.collected.builtinEntry .integer (.integer 37) sequence.builtinRead
    (Core.Word.ofNatModulo 37) (RecursiveStageRegistry.scope stages.sidecar [] first.initial.header.function)

variable {issued : Issued fixture.recipe} {stages : ObservedStages fixture observed.makeRow}
  {sequence : ObservedSequence fixture observed}

theorem sequence_meaning (profile : Observed fixture)
    (stages : ObservedStages fixture observed.makeRow) (sequence : ObservedSequence fixture observed) :
    ∃ issued : Issued fixture.recipe, Nonempty (SequenceMeaning issued stages sequence) := by
  obtain ⟨issued, ⟨first⟩⟩ := first_meaning profile stages sequence.first
  let scope := RecursiveStageRegistry.scope stages.sidecar [] first.initial.header.function
  obtain ⟨factory⟩ := named_meaning first.after observed.makeRow sequence.factory
  obtain ⟨builtin⟩ := builtin_meaning factory.after sequence.builtin
  obtain ⟨named⟩ := named_meaning builtin.after observed.readRow sequence.named
  obtain ⟨construction⟩ := construction_meaning named.after named.entry factory.entry first.entry builtin.entry
    (by simp) (by simp) (by simp) (by simp)
    (named.entryType.trans named.selected.read_type) (factory.entryType.trans factory.selected.make_type)
    first.entryType builtin.entryType named.handleEq factory.handleEq first.handleEq builtin.handleEq sequence.construction scope
  have newMember : construction.collected.newEntry ∈
      ((([first.entry] ++ [factory.entry]) ++ [builtin.entry]) ++ [named.entry]) ++ construction.added := by
    simp [construction.collected.ordered]
  have priorMember : construction.collected.priorEntry ∈
      ((([first.entry] ++ [factory.entry]) ++ [builtin.entry]) ++ [named.entry]) ++ construction.added := by
    simp [construction.collected.ordered]
  have factoryMember : construction.collected.factoryEntry ∈
      ((([first.entry] ++ [factory.entry]) ++ [builtin.entry]) ++ [named.entry]) ++ construction.added := by
    simp [construction.collected.ordered]
  have builtinMember : construction.collected.builtinEntry ∈
      ((([first.entry] ++ [factory.entry]) ++ [builtin.entry]) ++ [named.entry]) ++ construction.added := by
    simp [construction.collected.ordered]
  have unitInput : RecursiveNamedPublicFunctionHistoryInputs.Input
      (((([first.entry] ++ [factory.entry]) ++ [builtin.entry]) ++ [named.entry]) ++ construction.added)
      first.initial.header.function.context .unit .unit .unit :=
    .data ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
      ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
  have wordInput : RecursiveNamedPublicFunctionHistoryInputs.Input
      (((([first.entry] ++ [factory.entry]) ++ [builtin.entry]) ++ [named.entry]) ++ construction.added)
      first.initial.header.function.context .word (.word interveningSeed) (.word interveningSeed) :=
    .data ⟨.word interveningSeed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word interveningSeed⟩
      ⟨.word interveningSeed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word interveningSeed⟩
  have integerInput : RecursiveNamedPublicFunctionHistoryInputs.Input
      (((([first.entry] ++ [factory.entry]) ++ [builtin.entry]) ++ [named.entry]) ++ construction.added)
      first.initial.header.function.context .integer (.integer 37) (.integer 37) :=
    .data ⟨.integer 37, by simp [SourceCoreIndexedSession.DataInput.publicValue], .integer 37⟩
      ⟨.integer 37, by simp [SourceCoreIndexedSession.DataInput.publicValue], .integer 37⟩
  obtain ⟨newRead⟩ := word_meaning construction.after construction.collected.newEntry newMember
    construction.collected.newType construction.collected.newHandle sequence.construction.newType unitInput
    sequence.newRead sequence.newValue scope
  obtain ⟨intervening⟩ := success_meaning newRead.after construction.collected.factoryEntry factoryMember
    construction.collected.factoryType construction.collected.factoryHandle wordInput sequence.intervening scope
  obtain ⟨priorRead⟩ := word_meaning intervening.after construction.collected.priorEntry priorMember
    construction.collected.priorType construction.collected.priorHandle sequence.construction.priorType unitInput
    sequence.priorRead sequence.priorValue scope
  obtain ⟨builtinRead⟩ := word_meaning priorRead.after construction.collected.builtinEntry builtinMember
    construction.collected.builtinType construction.collected.builtinHandle sequence.construction.builtinType integerInput
    sequence.builtinRead sequence.builtinValue scope
  exact ⟨issued, ⟨⟨first, factory, builtin, named, construction, newRead, intervening, priorRead, builtinRead⟩⟩⟩

theorem SequenceMeaning.issuance_heap (meaning : SequenceMeaning issued stages sequence) :
    meaning.named.after.heap = meaning.first.after.heap :=
  meaning.named.heapEq.trans (meaning.builtin.heapEq.trans meaning.factory.heapEq)

theorem SequenceMeaning.selected_handles (meaning : SequenceMeaning issued stages sequence) :
    meaning.construction.collected.newEntry.handle ≠ meaning.construction.collected.priorEntry.handle ∧
    meaning.construction.collected.priorEntry.handle = meaning.first.entry.handle ∧
    meaning.construction.collected.factoryEntry.handle = meaning.factory.entry.handle ∧
    meaning.construction.collected.builtinEntry.handle = meaning.builtin.entry.handle := by
  rw [meaning.construction.collected.newHandle, meaning.construction.collected.priorHandle,
    meaning.construction.collected.factoryHandle, meaning.construction.collected.builtinHandle,
    meaning.first.handleEq, meaning.factory.handleEq, meaning.builtin.handleEq]
  exact ⟨sequence.construction.distinct, sequence.construction.priorSame,
    sequence.construction.factorySame, sequence.construction.builtinSame⟩

/-- Six executions have ordinary Dynamic meanings. The three intervening
issuances retain their exact Source callable identities and unchanged heaps. -/
structure PlainMeaning (meaning : SequenceMeaning issued stages sequence) : Prop where
  first : SelectedCompilationPublicSessionState.PlainValue meaning.first.initial.header meaning.first.initial.header
    (RecursiveStageRegistry.scope stages.sidecar [] meaning.first.initial.header.function)
    ⟨[]⟩ [.word seed] meaning.first.entry.source meaning.first.after.heap
  construction : Dynamic.CallableApplies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    meaning.first.initial.header.function.context
    (RecursiveStageRegistry.scope stages.sidecar [] meaning.first.initial.header.function).evidence
    (Staging.Recursive.callableEvidence meaning.named.entry.source)
    meaning.named.after.heap meaning.named.entry.source meaning.construction.arguments
    meaning.construction.source meaning.construction.after.heap
  newRead : Dynamic.CallableApplies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    meaning.first.initial.header.function.context
    (RecursiveStageRegistry.scope stages.sidecar [] meaning.first.initial.header.function).evidence
    (Staging.Recursive.callableEvidence meaning.construction.collected.newEntry.source)
    meaning.construction.after.heap meaning.construction.collected.newEntry.source meaning.newRead.arguments
    (.word secondSeed) meaning.newRead.after.heap
  intervening : Dynamic.CallableApplies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    meaning.first.initial.header.function.context
    (RecursiveStageRegistry.scope stages.sidecar [] meaning.first.initial.header.function).evidence
    (Staging.Recursive.callableEvidence meaning.construction.collected.factoryEntry.source)
    meaning.newRead.after.heap meaning.construction.collected.factoryEntry.source meaning.intervening.arguments
    meaning.intervening.source meaning.intervening.after.heap
  priorRead : Dynamic.CallableApplies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    meaning.first.initial.header.function.context
    (RecursiveStageRegistry.scope stages.sidecar [] meaning.first.initial.header.function).evidence
    (Staging.Recursive.callableEvidence meaning.construction.collected.priorEntry.source)
    meaning.intervening.after.heap meaning.construction.collected.priorEntry.source meaning.priorRead.arguments
    (.word seed) meaning.priorRead.after.heap
  builtinRead : Dynamic.CallableApplies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    meaning.first.initial.header.function.context
    (RecursiveStageRegistry.scope stages.sidecar [] meaning.first.initial.header.function).evidence
    (Staging.Recursive.callableEvidence meaning.construction.collected.builtinEntry.source)
    meaning.priorRead.after.heap meaning.construction.collected.builtinEntry.source meaning.builtinRead.arguments
    (.word (Core.Word.ofNatModulo 37)) meaning.builtinRead.after.heap

theorem SequenceMeaning.plain (meaning : SequenceMeaning issued stages sequence) : PlainMeaning meaning :=
  ⟨meaning.first.trace.value_plain, meaning.construction.trace.sound.value_plain,
    meaning.newRead.trace.sound.value_plain, meaning.intervening.trace.sound.value_plain,
    meaning.priorRead.trace.sound.value_plain, meaning.builtinRead.trace.sound.value_plain⟩

section Forward
variable {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List Entry} {handle : SourceCorePublicValues.Handle} {argument : SourceCorePublicValues.Value}

def OutputForward (_before : issued.State anchor session entries)
    (_call : ObservedInvocation session handle argument) (result : TypeSystem.Ty)
    (source : Dynamic.Value) (after : Dynamic.Heap) : Prop :=
  ∃ checkpoint, session.startHandlePacked handle argument runOptions.inputValidationFuel = .ok checkpoint ∧
    SelectedCompilationPublicSessionDirectOutputForward.ForwardAt issued.catalog.rows anchor
      issued.initial issued.support.profile fixture.recipe entries result checkpoint source after

def WordForward (_before : issued.State anchor session entries)
    (_call : ObservedInvocation session handle argument) (word : Core.Word) (after : Dynamic.Heap) : Prop :=
  ∃ checkpoint, session.startHandlePacked handle argument runOptions.inputValidationFuel = .ok checkpoint ∧
    SelectedCompilationPublicSessionDirectWordForward.ForwardAt issued.catalog.rows anchor
      issued.initial issued.support.profile fixture.recipe entries word checkpoint after
end Forward

structure ForwardMeaning (meaning : SequenceMeaning issued stages sequence) : Prop where
  first : SelectedCompilationPublicSessionInitialForward.ForwardAt issued.catalog.rows meaning.first.initial.header
    meaning.first.initial.header issued.support (firstCall sequence.first).toCall.toStartedCall
    meaning.first.entry.source meaning.first.after.heap
  construction : OutputForward meaning.named.after sequence.construction.toObservedInvocation
    (containerType fixture.dataType) meaning.construction.source meaning.construction.after.heap
  newRead : WordForward meaning.construction.after sequence.newRead secondSeed meaning.newRead.after.heap
  intervening : OutputForward meaning.newRead.after sequence.intervening closureType meaning.intervening.source meaning.intervening.after.heap
  priorRead : WordForward meaning.intervening.after sequence.priorRead seed meaning.priorRead.after.heap
  builtinRead : WordForward meaning.priorRead.after sequence.builtinRead (Core.Word.ofNatModulo 37) meaning.builtinRead.after.heap

theorem SequenceMeaning.forward (meaning : SequenceMeaning issued stages sequence) : ForwardMeaning meaning := by
  have initialReady := (SourceCoreExecution.Bootstrap.ReadyAt.single sequence.first.ready).exportsReady sequence.first.authority
  have firstReady := sequence.first.executed.exportsReady initialReady
  have factoryReady := sequence.factory.issued.exportsReady firstReady
  have builtinReady := sequence.builtin.issued.exportsReady factoryReady
  have namedReady := sequence.named.issued.exportsReady builtinReady
  have constructionReady := sequence.construction.executed.exportsReady namedReady
  have newReady := sequence.newRead.executed.exportsReady constructionReady
  exact ⟨meaning.first.forward, meaning.construction.forward namedReady, meaning.newRead.forward,
    meaning.intervening.forward newReady, meaning.priorRead.forward, meaning.builtinRead.forward⟩

theorem closed_sequence_forward_meaning (profile : Observed fixture)
    (stages : ObservedStages fixture observed.makeRow) (sequence : ObservedSequence fixture observed) :
    ∃ (issued : Issued fixture.recipe) (meaning : SequenceMeaning issued stages sequence),
      meaning.named.after.heap = meaning.first.after.heap ∧
      meaning.construction.collected.newEntry.handle ≠ meaning.construction.collected.priorEntry.handle ∧
      meaning.construction.collected.priorEntry.handle = meaning.first.entry.handle ∧
      meaning.construction.collected.factoryEntry.handle = meaning.factory.entry.handle ∧
      meaning.construction.collected.builtinEntry.handle = meaning.builtin.entry.handle ∧
      ForwardMeaning meaning ∧ PlainMeaning meaning := by
  obtain ⟨issued, ⟨meaning⟩⟩ := sequence_meaning profile stages sequence
  obtain ⟨distinct, prior, factory, builtin⟩ := meaning.selected_handles
  exact ⟨issued, meaning, meaning.issuance_heap, distinct, prior, factory, builtin, meaning.forward, meaning.plain⟩

def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let profile ← observe fixture
  let stages ← observeStages fixture observed.makeRow
  let sequence ← observeSequence fixture observed
  have _meaning := closed_sequence_forward_meaning profile stages sequence
  unless fixture.recipe.compiled.indexed.base.functions.length == 2 && profile.value.table.rows.length == 2 do
    throw (IO.userError "constructor profile changed original cache2/table2")
  let stores := [sequence.first.session.heapSize, sequence.first.completion.session.heapSize,
    sequence.factory.completion.session.heapSize, sequence.builtin.completion.session.heapSize,
    sequence.named.completion.session.heapSize, sequence.construction.completion.session.heapSize,
    sequence.newRead.completion.session.heapSize, sequence.intervening.completion.session.heapSize,
    sequence.priorRead.completion.session.heapSize, sequence.builtinRead.completion.session.heapSize]
  unless stores == [3,9,9,9,9,27,30,36,39,39] do
    throw (IO.userError s!"constructor profile stores changed: {reprStr stores}")
  IO.println s!"CONSTRUCTOR_COMPILER_PROFILE_FORWARD_PASS: original checker1000/cache2/table2; one complete profile and automatic catalog; original nine operations and ordered nested payload; exact three issuance identities, six Dynamic execution outcomes, sufficient fuel for every output selection and later word outputs; new20/factory30export/old10/builtin37; stores {reprStr stores}"

end Tests.SourceCoreConstructorCalls.CompilerProfile
end

section
-- leanmerge: from Solcore.Test.SourceCoreConstructorCallsPublicExecution
/-! The actual constructor creates a fresh capture by an indirect child call,
exports it beside three existing callable kinds, and reuses the selected
handles through the exact subsequent sessions and Source heaps. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreConstructorCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

structure SequenceWitness {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (makeStages : ObservedStages fixture observed.makeRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) where
  support : PublicSupports receiver
  first : Entry
  factory : Entry
  builtin : Entry
  named : Entry
  firstType : first.sourceType = closureType
  factoryType : factory.sourceType = makerType
  builtinType : builtin.sourceType = convertType
  namedType : named.sourceType = .function packedType (containerType fixture.dataType)
  firstHandle : first.handle = sequence.first.handle
  factoryHandle : factory.handle = sequence.factory.handle
  builtinHandle : builtin.handle = sequence.builtin.handle
  namedHandle : named.handle = sequence.named.handle
  source : Dynamic.Value
  added : List Entry
  collected : Collected observed source sequence.construction.newOutput sequence.construction.priorOutput
    sequence.construction.factoryOutput sequence.construction.builtinOutput added
  initial : RetainedState support sequence.first.completion.session [first]
  issuedState : RetainedState support sequence.named.completion.session [first, factory, builtin, named]
  collectedState : RetainedState support sequence.construction.completion.session ([first, factory, builtin, named] ++ added)
  newReadState : RetainedState support sequence.newRead.completion.session ([first, factory, builtin, named] ++ added)
  interveningState : RetainedState support sequence.intervening.completion.session ([first, factory, builtin, named] ++ added)
  priorReadState : RetainedState support sequence.priorRead.completion.session ([first, factory, builtin, named] ++ added)
  finalState : RetainedState support sequence.builtinRead.completion.session ([first, factory, builtin, named] ++ added)
  firstTrace : SourceCall support support.makeHeader.header
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    ⟨[]⟩ [.word seed] (.value first.source) initial.heap
  issuedHeap : issuedState.heap = initial.heap
  constructionTrace : SourceConstruction support
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    issuedState.heap named.source factory.source first.source builtin.source source collectedState.heap
  newArguments : List Dynamic.Value
  newPacking : Dynamic.ValuesPack newArguments .unit
  newReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    collectedState.heap collected.newEntry.source newArguments (.value (.word secondSeed)) newReadState.heap
  interveningArguments : List Dynamic.Value
  interveningPacking : Dynamic.ValuesPack interveningArguments (.word interveningSeed)
  interveningSource : Dynamic.Value
  interveningTrace : SourceInvocation support
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    newReadState.heap collected.factoryEntry.source interveningArguments (.value interveningSource) interveningState.heap
  priorArguments : List Dynamic.Value
  priorPacking : Dynamic.ValuesPack priorArguments .unit
  priorReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    interveningState.heap collected.priorEntry.source priorArguments (.value (.word seed)) priorReadState.heap
  builtinArguments : List Dynamic.Value
  builtinPacking : Dynamic.ValuesPack builtinArguments (.integer 37)
  builtinReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    priorReadState.heap collected.builtinEntry.source builtinArguments (.value (.word (Core.Word.ofNatModulo 37))) finalState.heap

theorem sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (admission : ObservedProgramCertificate fixture observed)
    (makeStages : ObservedStages fixture observed.makeRow)
    (readStages : ObservedStages fixture observed.readRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    Nonempty (SequenceWitness makeStages sequence receiver) := by
  obtain ⟨support⟩ := static_supports fixture observed admission makeStages readStages receiver
  let scope := RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function
  obtain ⟨first, firstType, firstHandle, _firstHandleType, initial, firstTrace⟩ :=
    first_meaning_typed_handle extra support makeStages sequence.first
  obtain ⟨factory, factoryType, factoryHandle, _factoryHandleType, _factorySource, factoryState, factoryHeap⟩ :=
    remember_maker initial sequence.factory
  obtain ⟨builtin, builtinType, builtinHandle, _builtinHandleType, _builtinSource, builtinState, builtinHeap⟩ :=
    remember_builtin factoryState sequence.builtin
  obtain ⟨named, namedType, namedHandle, _namedHandleType, _namedSource, issuedState, issuedHeap⟩ :=
    remember_named builtinState sequence.named
  obtain ⟨source, added, collected, collectedState, constructionTrace⟩ :=
    collect issuedState named factory first builtin (by simp) (by simp) (by simp) (by simp)
      namedType factoryType firstType builtinType namedHandle factoryHandle firstHandle builtinHandle
      sequence.construction scope
  have newMember : collected.newEntry ∈ [first, factory, builtin, named] ++ added := by simp [collected.ordered]
  have priorMember : collected.priorEntry ∈ [first, factory, builtin, named] ++ added := by simp [collected.ordered]
  have factoryMember : collected.factoryEntry ∈ [first, factory, builtin, named] ++ added := by simp [collected.ordered]
  have builtinMember : collected.builtinEntry ∈ [first, factory, builtin, named] ++ added := by simp [collected.ordered]
  have unitInput : RecursiveNamedPublicFunctionHistoryInputs.Input
      ([first, factory, builtin, named] ++ added) support.makeHeader.header.function.context .unit .unit .unit :=
    .data ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
      ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
  have wordInput : RecursiveNamedPublicFunctionHistoryInputs.Input
      ([first, factory, builtin, named] ++ added) support.makeHeader.header.function.context
      .word (.word interveningSeed) (.word interveningSeed) :=
    .data ⟨.word interveningSeed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word interveningSeed⟩
      ⟨.word interveningSeed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word interveningSeed⟩
  have integerInput : RecursiveNamedPublicFunctionHistoryInputs.Input
      ([first, factory, builtin, named] ++ added) support.makeHeader.header.function.context
      .integer (.integer 37) (.integer 37) :=
    .data ⟨.integer 37, by simp [SourceCoreIndexedSession.DataInput.publicValue], .integer 37⟩
      ⟨.integer 37, by simp [SourceCoreIndexedSession.DataInput.publicValue], .integer 37⟩
  obtain ⟨newArguments, newReadState, newPacking, newReadTrace⟩ := invoke_word collectedState collected.newEntry
    newMember collected.newType collected.newHandle sequence.construction.newType unitInput
    sequence.newRead sequence.newValue scope
  obtain ⟨interveningArguments, interveningSource, interveningState, interveningPacking, interveningTrace⟩ :=
    invoke_success newReadState collected.factoryEntry factoryMember collected.factoryType collected.factoryHandle
      wordInput sequence.intervening scope
  obtain ⟨priorArguments, priorReadState, priorPacking, priorReadTrace⟩ := invoke_word interveningState collected.priorEntry
    priorMember collected.priorType collected.priorHandle sequence.construction.priorType unitInput
    sequence.priorRead sequence.priorValue scope
  obtain ⟨builtinArguments, finalState, builtinPacking, builtinReadTrace⟩ := invoke_word priorReadState collected.builtinEntry
    builtinMember collected.builtinType collected.builtinHandle sequence.construction.builtinType integerInput
    sequence.builtinRead sequence.builtinValue scope
  exact ⟨{
    support := support
    first := first
    factory := factory
    builtin := builtin
    named := named
    firstType := firstType
    factoryType := factoryType
    builtinType := builtinType
    namedType := namedType
    firstHandle := firstHandle
    factoryHandle := factoryHandle
    builtinHandle := builtinHandle
    namedHandle := namedHandle
    source := source
    added := added
    collected := collected
    initial := initial
    issuedState := issuedState
    collectedState := collectedState
    newReadState := newReadState
    interveningState := interveningState
    priorReadState := priorReadState
    finalState := finalState
    firstTrace := firstTrace
    issuedHeap := issuedHeap.trans (builtinHeap.trans factoryHeap)
    constructionTrace := constructionTrace
    newArguments := newArguments
    newPacking := newPacking
    newReadTrace := newReadTrace
    interveningArguments := interveningArguments
    interveningPacking := interveningPacking
    interveningSource := interveningSource
    interveningTrace := interveningTrace
    priorArguments := priorArguments
    priorPacking := priorPacking
    priorReadTrace := priorReadTrace
    builtinArguments := builtinArguments
    builtinPacking := builtinPacking
    builtinReadTrace := builtinReadTrace
  }⟩

theorem closed_sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (admission : ObservedProgramCertificate fixture observed)
    (makeStages : ObservedStages fixture observed.makeRow)
    (readStages : ObservedStages fixture observed.readRow)
    (sequence : ObservedSequence fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed, Nonempty (SequenceWitness makeStages sequence receiver) := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  exact ⟨receiver, sequence_meaning fixture observed extra admission makeStages readStages sequence receiver⟩

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let extra ← observeMake fixture observed
  let admission ← observeProgramCertificate fixture observed
  let makeStages ← observeStages fixture observed.makeRow
  let readStages ← observeStages fixture observed.readRow
  let sequence ← observeSequence fixture observed
  have _automatic := admission.automatic_catalog_initial
  have _meaning := closed_sequence_meaning fixture observed extra admission makeStages readStages sequence
  IO.println "Constructor with indirect child: new capture20, retained factory30, old capture10, builtin37; exact Source traces, ordered collected payloads and returned histories proved"

end Tests.SourceCoreConstructorCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreConstructorCallsForward
/-! Independent Source success also implies public nominal-constructor export and ordered
nested collection for every sufficient execution and output fuel budget. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreConstructorCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)
open RecursiveNamedPublicNestedOutputSelections (Selection Selected)

def SelectedAt {fixture : CompiledFixture} {publicArtifact : SourceCoreExecution.Artifact}
    (completion : SourceCoreExecution.Completion publicArtifact)
    (selection : Selection (containerType fixture.dataType) completion.value) (source : Dynamic.Value)
    (outputFuel : Nat) (added : List Entry) : Prop :=
  ∃ (artifact : SourceCoreIndexedSession.Artifact) (actual : SourceCoreIndexedSession.Completion artifact)
    (native : Core.Value) (type : Core.Ty), completion.IndexedAt actual ∧
    Selected fixture.recipe.compiled.compatible.checked actual.session selection source native type outputFuel added

def ForwardCollectionAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (entries : List Entry) (handle : SourceCorePublicValues.Handle)
    (argument : SourceCorePublicValues.Value) (source : Dynamic.Value) (after : Dynamic.Heap) : Prop :=
  ∃ checkpoint : SourceCoreExecution.Checkpoint artifact,
    session.startHandlePacked handle argument runOptions.inputValidationFuel = .ok checkpoint ∧
    ∃ requiredExecution requiredOutput,
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
        requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
        checkpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ completion : SourceCoreExecution.Completion artifact,
          outcome = .succeeded completion ∧ completion.session.ExportsReady ∧
          ∀ selection : Selection (containerType fixture.dataType) completion.value,
            ∃ (added : List Entry) (next : RetainedState support completion.session (entries ++ added)),
              next.heap = after ∧ added.map Entry.handle = selection.handles ∧
              SelectedAt (fixture := fixture) completion selection source outputFuel added

theorem SequenceWitness.forward_collection {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {makeStages : ObservedStages fixture observed.makeRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness makeStages sequence receiver) :
    ForwardCollectionAt meaning.support sequence.named.completion.session
      [meaning.first, meaning.factory, meaning.builtin, meaning.named]
      sequence.named.handle (packedArgument sequence.factory.handle sequence.first.handle sequence.builtin.handle)
      meaning.source meaning.collectedState.heap := by
  let state := meaning.issuedState
  have initialReady := (SourceCoreExecution.Bootstrap.ReadyAt.single sequence.first.ready).exportsReady sequence.first.authority
  have firstReady := sequence.first.executed.exportsReady initialReady
  have factoryReady := sequence.factory.issued.exportsReady firstReady
  have builtinReady := sequence.builtin.issued.exportsReady factoryReady
  have exportsReady := sequence.named.issued.exportsReady builtinReady
  obtain ⟨publicCheckpoint, accepted, _resumed⟩ := sequence.construction.executed
  have member : meaning.named ∈ [meaning.first, meaning.factory, meaning.builtin, meaning.named] := by simp
  have input := construction_input
    (entries := [meaning.first, meaning.factory, meaning.builtin, meaning.named])
    (context := meaning.support.makeHeader.header.function.context)
    meaning.factory meaning.first meaning.builtin (by simp) (by simp) (by simp)
    meaning.factoryType meaning.firstType meaning.builtinType meaning.factoryHandle meaning.firstHandle meaning.builtinHandle
  obtain ⟨sources, size, packing, trace⟩ := meaning.constructionTrace
  refine ⟨publicCheckpoint, accepted, ?_⟩
  exact RecursiveNamedPublicPhysicalSessionDirectOutputForward.forward_call meaning.support.program
    fixture.recipePrepared state meaning.named member meaning.namedType input
    (by simpa only [meaning.namedHandle] using accepted) exportsReady packing trace


def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let extra ← observeMake fixture observed
  let admission ← observeProgramCertificate fixture observed
  let makeStages ← observeStages fixture observed.makeRow
  let readStages ← observeStages fixture observed.readRow
  let sequence ← observeSequence fixture observed
  have _automatic := admission.automatic_catalog_initial
  have _meaning : ∃ receiver : ObservedReceiver fixture observed,
      ∃ meaning : SequenceWitness makeStages sequence receiver,
        ForwardCollectionAt meaning.support sequence.named.completion.session
          [meaning.first, meaning.factory, meaning.builtin, meaning.named]
          sequence.named.handle (packedArgument sequence.factory.handle sequence.first.handle sequence.builtin.handle)
          meaning.source meaning.collectedState.heap := by
    obtain ⟨receiver, witness⟩ := closed_sequence_meaning fixture observed extra admission makeStages readStages sequence
    obtain ⟨witness⟩ := witness
    exact ⟨receiver, witness, witness.forward_collection⟩
  IO.println "Constructor recursive child and payload collection: independent Source meaning, sufficient public fuel, retained callable reuse20/30export/10/37 proved"

end Tests.SourceCoreConstructorCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreConstructorNativeTyping
/-! Registered production headers and recursively extracted child code supply
native typing. The consumer retains raw metadata and source constructor facts,
instead of attempting to reconstruct either from a native named-data type. -/
set_option autoImplicit false
namespace Tests.SourceCoreConstructorNativeTyping
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleExpressionScalarNativeTyping CompatibleExpressionConstructorNativeTyping

/-- An actual contextual compiler result needs no separately supplied child
code typing, even with arbitrary hidden slots and extra ambient definitions. -/
theorem actual_contextual_native
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {compilation : SourceCoreFunctions.Context}
    {native : Option SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {compileFuel readFuel : Nat}
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    {sourceContext : SourceSemantics.Context} {definitions : DataEnvironment}
    (visibleTypes : ScopeWellFormed values.checked.catalog.definitions scope)
    (administrative : Core.Context)
    (ordinary : CompatibleExpressionConstructors.Ordinary source locals compilation.owner)
    (unique : NodeOccurrencesUnique source)
    (closed : sourceContext.typeVariables = []) (residual : sourceContext.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (syntaxTree : CompatibleExpressionConstructors.Syntax source id)
    (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source sourceContext id node.type)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression program representation signatures locals parents assignments
      diagnostics compilation native parent skipInitializer compileFuel source scope id reasonAt = .ok lowered)
    (extension : values.checked.catalog.definitions.Extends definitions) :
    NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered :=
  CompatibleExpressionConstructorNativeTyping.contextual_native visibleTypes administrative
    ordinary unique closed residual declarations syntaxTree found typed readPolicy lowerPolicy leafPolicy accepted extension

/-- Recursive constructor children close their own native typing. Only the
existing source-static trees and actual registered header are inputs. -/
theorem actual_header_native
    {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {context : SourceSemantics.Context} {solved : List SolvedRequirement}
    {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {node : ExpressionNode} {instantiation : DataConstructorInstantiation}
    {ids : List ExpressionId} {tag : ConstructorId} {header : Word}
    {codes : List SourceCoreBasic.LoweredExpr} {definitions : DataEnvironment}
    (visibleTypes : ScopeWellFormed values.checked.catalog.definitions scope)
    (administrative : Core.Context)
    (receipt : CompatibleExpressionConstructors.Header values source id node instantiation tag header codes)
    (form : node.form = .constructor instantiation ids)
    (valid : SourceSemantics.DataConstructorInstantiation.Valid context instantiation)
    (count : ids.length = instantiation.payloadTypes.length)
    (nodes : CompatibleExpressionConstructors.Nodes source ids instantiation.payloadTypes codes)
    (children : ∀ child code, (child, code) ∈ ids.zip codes →
      CompatibleExpressionConstructors.Tree fuel values source context solved reasonAt scope child code)
    (extension : values.checked.catalog.definitions.Extends definitions) :
    NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative)
      ⟨.namedData tag.owner,
        SourceCoreCompatibleDataExpressions.construct tag header (SourceCoreCalls.packArguments codes).expression⟩ :=
  constructors_native_at visibleTypes administrative extension
    (.constructor receipt form valid count nodes children)

/-- Native constructor typing requires the exact registered payload shape.
A type for its inhabited argument cannot invent an absent constructor. -/
theorem absent_constructor_rejected (tag : ConstructorId) (header : Word) (context : Core.Context) :
    ¬ HasType context (SourceCoreCompatibleDataExpressions.construct tag header
      (LanguageResult.success .unit)) (LanguageResult.resultType (.namedData tag.owner)) [] := by
  intro typed
  simp only [SourceCoreCompatibleDataExpressions.construct, LanguageResult.bind] at typed
  cases typed with
  | caseE _ failed _ =>
    cases failed with
    | inLeft registered _ =>
      cases registered with
      | namedData found => cases found

end Tests.SourceCoreConstructorNativeTyping
end
