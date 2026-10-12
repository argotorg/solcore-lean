import Solcore.Test.SourceCoreOperatorCallsSource
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
