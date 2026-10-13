import Solcore.Test.SourceCoreRecursiveIndexSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreCanonicalScoped
open Solcore Frontend SourceInference SourceSemantics
abbrev Read := Tests.SourceCoreNamedBranch.Read
abbrev DirectCall := Tests.SourceCoreRecursiveIndex.DirectCall
abbrev IdentityShape (function : CheckedFunction) (signature : ProgramFunctionSignature) :=
  Tests.SourceCoreRecursiveIndex.IdentityShape function signature .word
abbrev parameterType : TypeSystem.Ty := .product .word (.product .bool .bool)
abbrev closureType : TypeSystem.Ty := .function parameterType .word
private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)
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


structure RelayShape (function : CheckedFunction) (signature identity : ProgramFunctionSignature) where
  binder : TypedBinder
  localBinder : TypedBinder
  initialRead : Read function.typedBody binder .word
  initial : DirectCall function.typedBody identity initialRead.node.id .word .word
  finalRead : Read function.typedBody localBinder .word
  initialized : StatementNode
  statement : StatementNode
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [.word]
  inputs : function.typedBody.inputs = [binder]
  binderRequirements : binder.schemeRequirements = []
  localScheme : localBinder.scheme = .mono .word
  localRequirements : localBinder.schemeRequirements = []
  localOwner : localBinder.id.owner = function.typedBody.owner
  localDistinct : localBinder.id ≠ binder.id
  localOrdinary : localBinder.comptime = false
  roots : function.typedBody.roots = [.statement initialized.id, .statement statement.id]
  initializedFound : function.typedBody.lookupStatement? initialized.id = some initialized
  initializedForm : initialized.form = .letDecl localBinder (some initial.value.node.id)
  initializedType : initialized.type = .unit
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some finalRead.node.id)
  statementType : statement.type = .word

def RelayShape.nodeList {function signature identity} (shape : RelayShape function signature identity) : List SourceInference.Node :=
  [.expression shape.initialRead.node, .expression shape.initial.callee.node, .expression shape.initial.value.node,
    .statement shape.initialized, .expression shape.finalRead.node, .statement shape.statement]

theorem RelayShape.statementTyping {function signature identity}
    (shape : RelayShape function signature identity) (signatures : ProgramSignatures)
    (identityMember : identity ∈ signatures.functions) : CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.initialized.id, shape.statement.id] := statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let ordinary : StatementFacts := {type:=.unit, hasValue:=false, sawReturn:=false, control:=.ordinary .unit}
  let returned : StatementFacts := {type:=.word, hasValue:=true, sawReturn:=true, control:=.returned}
  refine ⟨BodyFacts.cons ordinary (BodyFacts.singleton returned), rfl, ?_⟩
  intro lexical extension
  rw [shape.inputs, shape.inputTypes] at extension
  cases extension with
  | cons scheme head tail =>
    cases tail
    have binders : TypeParameterBindersWellFormed lexical := by
      rw [TypeParameterBindersWellFormed, head.context_fields.2.2.1]
      simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
        Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
    have fields : lexical.signatures = signatures := by rw [head.context_fields.1]; rfl
    have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
    let locals := lexical.withLocal shape.localBinder.id shape.localBinder.scheme shape.localBinder.schemeRequirements
    have localExtended : BinderExtends function.typedBody.owner lexical shape.localBinder locals := by
      apply BinderExtends.intro
      · exact {
          owned := shape.localOwner
          scheme := shape.localScheme.symm ▸ SchemeWellFormed.monoAdmissible word
          quantified_fresh := by rw [shape.localScheme]; simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]
          monomorphic_requirements_empty := fun _ => shape.localRequirements }
      · cases head
        simp [LocalFresh, Context.withLocal, checkedBodyContext, declarationContext,
          Context.ofSignatures, Context.forDeclaration, Context.withAssumptions,
          Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.localDistinct]
    have initialRead := shape.initialRead.typed scheme shape.binderRequirements word
      head.local_self head.local_scheme_requirements_self
    have initial := shape.initial.typed (fields ▸ identityMember) word initialRead
    have localWord : TypeAdmissible locals .word := ⟨binders, .builtin .word⟩
    have finalRead := shape.finalRead.typed shape.localScheme shape.localRequirements localWord
      localExtended.local_self localExtended.local_scheme_requirements_self
    have initialized : StatementHasType function.typedBody ⟨.word,0⟩ lexical shape.initialized.id locals ordinary := by
      apply StatementHasType.letInitialized (lookupStatement?_sound shape.initializedFound) shape.initializedForm
      · simpa only [shape.localScheme, TypeSystem.Scheme.mono] using initial
      · rw [shape.localScheme]; rfl
      · rw [shape.localScheme]; rfl
      · exact localExtended
      · exact shape.initializedType
    exact ⟨_, .cons initialized (.singleton (.returnValue (lookupStatement?_sound shape.statementFound)
      shape.statementForm finalRead shape.statementType))⟩

structure FactoryShape (function : CheckedFunction) (signature identity relay : ProgramFunctionSignature) where
  binder : TypedBinder
  argument : TypedBinder
  flag : TypedBinder
  stop : TypedBinder
  previous : TypedBinder
  initialRead : Read function.typedBody binder .word
  initial : DirectCall function.typedBody relay initialRead.node.id .word .word
  conditionRead : Read function.typedBody flag .bool
  argumentRead : Read function.typedBody argument .word
  updated : DirectCall function.typedBody relay argumentRead.node.id .word .word
  stopRead : Read function.typedBody stop .bool
  previousRead : Read function.typedBody previous .word
  final : DirectCall function.typedBody identity previousRead.node.id .word .word
  initialized : StatementNode
  assignment : StatementNode
  resolution : AssignmentResolution
  flagAssignment : StatementNode
  flagResolution : AssignmentResolution
  loop : StatementNode
  innerReturn : StatementNode
  expression : ExpressionNode
  statement : StatementNode
  argumentScheme : argument.scheme = .mono .word
  argumentRequirements : argument.schemeRequirements = []
  argumentOwner : argument.id.owner = function.typedBody.owner
  argumentOrdinary : argument.comptime = false
  argumentDistinct : argument.id ≠ binder.id
  flagScheme : flag.scheme = .mono .bool
  flagRequirements : flag.schemeRequirements = []
  flagOwner : flag.id.owner = function.typedBody.owner
  flagOrdinary : flag.comptime = false
  flagDistinct : flag.id ≠ binder.id
  flagArgument : flag.id ≠ argument.id
  stopScheme : stop.scheme = .mono .bool
  stopRequirements : stop.schemeRequirements = []
  stopOwner : stop.id.owner = function.typedBody.owner
  stopOrdinary : stop.comptime = false
  stopDistinct : stop.id ≠ binder.id
  stopArgument : stop.id ≠ argument.id
  stopFlag : stop.id ≠ flag.id
  previousScheme : previous.scheme = .mono .word
  previousRequirements : previous.schemeRequirements = []
  previousOwner : previous.id.owner = function.typedBody.owner
  previousOrdinary : previous.comptime = false
  previousDistinct : previous.id ≠ binder.id
  previousArgument : previous.id ≠ argument.id
  previousFlag : previous.id ≠ flag.id
  previousStop : previous.id ≠ stop.id
  parameterNames : [argument.name, flag.name, stop.name].Nodup
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [closureType]
  inputs : function.typedBody.inputs = [binder]
  binderOwner : binder.id.owner = function.typedBody.owner
  binderRequirements : binder.schemeRequirements = []
  roots : function.typedBody.roots = [.statement statement.id]
  initializedFound : function.typedBody.lookupStatement? initialized.id = some initialized
  initializedForm : initialized.form = .letDecl previous (some initial.value.node.id)
  initializedType : initialized.type = .unit
  assignmentFound : function.typedBody.lookupStatement? assignment.id = some assignment
  assignmentForm : assignment.form = .assignValue resolution .equal updated.value.node.id
  assignmentType : assignment.type = .unit
  targetRoot : resolution.target.root = binder.id
  targetType : resolution.target.type = .word
  targetBare : resolution.target.projections = []
  assignmentRequirements : resolution.requirements = []
  flagAssignmentFound : function.typedBody.lookupStatement? flagAssignment.id = some flagAssignment
  flagAssignmentForm : flagAssignment.form = .assignValue flagResolution .equal stopRead.node.id
  flagAssignmentType : flagAssignment.type = .unit
  flagTargetRoot : flagResolution.target.root = flag.id
  flagTargetType : flagResolution.target.type = .bool
  flagTargetBare : flagResolution.target.projections = []
  flagAssignmentRequirements : flagResolution.requirements = []
  loopFound : function.typedBody.lookupStatement? loop.id = some loop
  loopForm : loop.form = .whileLoop conditionRead.node.id [assignment.id, flagAssignment.id]
  loopType : loop.type = .unit
  innerReturnFound : function.typedBody.lookupStatement? innerReturn.id = some innerReturn
  innerReturnForm : innerReturn.form = .returnStmt (some final.value.node.id)
  innerReturnType : innerReturn.type = .word
  expressionFound : function.typedBody.lookupExpression? expression.id = some expression
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  lambda : expression.form = .lambda [argument, flag, stop] .word [initialized.id, loop.id, innerReturn.id]
  expressionRaw : expression.rawType = closureType
  expressionType : expression.type = closureType
  requirements : expression.requirements = []
  coercions : expression.coercions = []
  returnStatement : statement.form = .returnStmt (some expression.id)
  statementType : statement.type = closureType

def FactoryShape.body {function signature identity relay} (shape : FactoryShape function signature identity relay) : List StatementId :=
  [shape.initialized.id, shape.loop.id, shape.innerReturn.id]

def FactoryShape.nodeList {function signature identity relay} (shape : FactoryShape function signature identity relay) : List SourceInference.Node :=
  [.expression shape.initialRead.node, .expression shape.initial.callee.node, .expression shape.initial.value.node,
    .statement shape.initialized, .expression shape.conditionRead.node, .expression shape.argumentRead.node,
    .expression shape.updated.callee.node, .expression shape.updated.value.node, .statement shape.assignment,
    .expression shape.stopRead.node, .statement shape.flagAssignment, .statement shape.loop,
    .expression shape.previousRead.node, .expression shape.final.callee.node, .expression shape.final.value.node,
    .statement shape.innerReturn, .expression shape.expression, .statement shape.statement]

theorem FactoryShape.statementTyping {function signature identity relay}
    (shape : FactoryShape function signature identity relay) (signatures : ProgramSignatures)
    (identityMember : identity ∈ signatures.functions) (relayMember : relay ∈ signatures.functions) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.statement.id] := statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type:=closureType, hasValue:=true, sawReturn:=true, control:=.returned}
  let ordinary : StatementFacts := {type:=.unit, hasValue:=false, sawReturn:=false, control:=.ordinary .unit}
  refine ⟨BodyFacts.singleton facts, rfl, ?_⟩
  intro lexical extension
  rw [shape.inputs, shape.inputTypes] at extension
  cases extension with
  | cons scheme head tail =>
    cases tail
    have binders : TypeParameterBindersWellFormed lexical := by
      rw [TypeParameterBindersWellFormed, head.context_fields.2.2.1]
      simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
        Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
    have fields : lexical.signatures = signatures := by rw [head.context_fields.1]; rfl
    have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
    have callable : TypeAdmissible lexical closureType :=
      ⟨binders, .function (.product (.builtin .word) (.product (.builtin .bool) (.builtin .bool))) (.builtin .word)⟩
    let arguments := lexical.withLocal shape.argument.id shape.argument.scheme shape.argument.schemeRequirements
    have argumentExtended : BinderExtends function.typedBody.owner lexical shape.argument arguments := by
      apply BinderExtends.intro
      · exact {
          owned := shape.argumentOwner
          scheme := shape.argumentScheme.symm ▸ SchemeWellFormed.monoAdmissible (show TypeAdmissible lexical .word from ⟨binders, .builtin .word⟩)
          quantified_fresh := by rw [shape.argumentScheme]; simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]
          monomorphic_requirements_empty := fun _ => shape.argumentRequirements }
      · cases head
        simp [LocalFresh, Context.withLocal, checkedBodyContext, declarationContext,
          Context.ofSignatures, Context.forDeclaration, Context.withAssumptions,
          Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.argumentDistinct]
    let flags := arguments.withLocal shape.flag.id shape.flag.scheme shape.flag.schemeRequirements
    have flagExtended : BinderExtends function.typedBody.owner arguments shape.flag flags := by
      apply BinderExtends.intro
      · exact {
          owned := shape.flagOwner
          scheme := shape.flagScheme.symm ▸ SchemeWellFormed.monoAdmissible (show TypeAdmissible arguments .bool from ⟨binders, .builtin .bool⟩)
          quantified_fresh := by rw [shape.flagScheme]; simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]
          monomorphic_requirements_empty := fun _ => shape.flagRequirements }
      · cases head
        simp [arguments, LocalFresh, Context.withLocal, checkedBodyContext, declarationContext,
          Context.ofSignatures, Context.forDeclaration, Context.withAssumptions,
          Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.flagDistinct, shape.flagArgument]
    let parameters := flags.withLocal shape.stop.id shape.stop.scheme shape.stop.schemeRequirements
    have stopExtended : BinderExtends function.typedBody.owner flags shape.stop parameters := by
      apply BinderExtends.intro
      · exact {
          owned := shape.stopOwner
          scheme := shape.stopScheme.symm ▸ SchemeWellFormed.monoAdmissible (show TypeAdmissible flags .bool from ⟨binders, .builtin .bool⟩)
          quantified_fresh := by rw [shape.stopScheme]; simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]
          monomorphic_requirements_empty := fun _ => shape.stopRequirements }
      · cases head
        simp [arguments, flags, LocalFresh, Context.withLocal, checkedBodyContext, declarationContext,
          Context.ofSignatures, Context.forDeclaration, Context.withAssumptions,
          Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.stopDistinct, shape.stopArgument, shape.stopFlag]
    let locals := parameters.withLocal shape.previous.id shape.previous.scheme shape.previous.schemeRequirements
    have previousExtended : BinderExtends function.typedBody.owner parameters shape.previous locals := by
      apply BinderExtends.intro
      · exact {
          owned := shape.previousOwner
          scheme := shape.previousScheme.symm ▸ SchemeWellFormed.monoAdmissible (show TypeAdmissible parameters .word from ⟨binders, .builtin .word⟩)
          quantified_fresh := by rw [shape.previousScheme]; simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]
          monomorphic_requirements_empty := fun _ => shape.previousRequirements }
      · cases head
        simp [arguments, flags, parameters, LocalFresh, Context.withLocal, checkedBodyContext, declarationContext,
          Context.ofSignatures, Context.forDeclaration, Context.withAssumptions,
          Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.previousDistinct, shape.previousArgument, shape.previousFlag, shape.previousStop]
    have parameterWord : TypeAdmissible parameters .word := ⟨binders, .builtin .word⟩
    have localWord : TypeAdmissible locals .word := ⟨binders, .builtin .word⟩
    have localBool : TypeAdmissible locals .bool := ⟨binders, .builtin .bool⟩
    have parameterFields : parameters.signatures = signatures := fields
    have localFields : locals.signatures = signatures := fields
    have initialRead := shape.initialRead.typed scheme shape.binderRequirements parameterWord
      (.tail shape.stopDistinct (.tail shape.flagDistinct (.tail shape.argumentDistinct head.local_self)))
      (.tail shape.stopDistinct (.tail shape.flagDistinct (.tail shape.argumentDistinct head.local_scheme_requirements_self)))
    have initial := shape.initial.typed (parameterFields ▸ relayMember) parameterWord initialRead
    have initializedTyped : StatementHasType function.typedBody ⟨.word,0⟩ parameters shape.initialized.id locals ordinary := by
      apply StatementHasType.letInitialized (lookupStatement?_sound shape.initializedFound) shape.initializedForm
      · simpa only [shape.previousScheme, TypeSystem.Scheme.mono] using initial
      · rw [shape.previousScheme]; rfl
      · rw [shape.previousScheme]; rfl
      · exact previousExtended
      · exact shape.initializedType
    have seedLookup : locals.LocalLookup shape.binder.id shape.binder.scheme :=
      .tail shape.previousDistinct (.tail shape.stopDistinct (.tail shape.flagDistinct (.tail shape.argumentDistinct head.local_self)))
    have flagLookup : locals.LocalLookup shape.flag.id shape.flag.scheme :=
      .tail shape.previousFlag (.tail shape.stopFlag flagExtended.local_self)
    have flagRequirements : locals.LocalSchemeRequirementsLookup shape.flag.id shape.flag.schemeRequirements :=
      .tail shape.previousFlag (.tail shape.stopFlag flagExtended.local_scheme_requirements_self)
    have conditionTyped := shape.conditionRead.typed shape.flagScheme shape.flagRequirements localBool flagLookup flagRequirements
    have argumentTyped := shape.argumentRead.typed shape.argumentScheme shape.argumentRequirements localWord
      (.tail shape.previousArgument (.tail shape.stopArgument (.tail shape.flagArgument argumentExtended.local_self)))
      (.tail shape.previousArgument (.tail shape.stopArgument (.tail shape.flagArgument argumentExtended.local_scheme_requirements_self)))
    have rhsTyped := shape.updated.typed (localFields ▸ relayMember) localWord argumentTyped
    have stopTyped := shape.stopRead.typed shape.stopScheme shape.stopRequirements localBool
      (.tail shape.previousStop stopExtended.local_self) (.tail shape.previousStop stopExtended.local_scheme_requirements_self)
    have previousTyped := shape.previousRead.typed shape.previousScheme shape.previousRequirements localWord
      previousExtended.local_self previousExtended.local_scheme_requirements_self
    have finalTyped := shape.final.typed (localFields ▸ identityMember) localWord previousTyped
    have writable : WritableLocal locals shape.resolution.target.root .word := by
      rw [shape.targetRoot]
      exact .intro seedLookup (scheme.symm ▸ SchemeWellFormed.monoAdmissible localWord)
        (by rw [scheme]; rfl) (by rw [scheme]; rfl)
    have assignmentTyped : SourceAssignmentHasType function.typedBody locals shape.resolution .equal shape.updated.value.node.id :=
      .equal (.intro writable (by rw [shape.targetBare]; exact .nil _) shape.targetType) rhsTyped shape.assignmentRequirements
    have statementTyped : StatementHasType function.typedBody ⟨.word,1⟩ locals shape.assignment.id locals ordinary :=
      .assignValue (lookupStatement?_sound shape.assignmentFound) shape.assignmentForm assignmentTyped shape.assignmentType
    have flagWritable : WritableLocal locals shape.flagResolution.target.root .bool := by
      rw [shape.flagTargetRoot]
      exact .intro flagLookup (shape.flagScheme.symm ▸ SchemeWellFormed.monoAdmissible localBool)
        (by rw [shape.flagScheme]; rfl) (by rw [shape.flagScheme]; rfl)
    have flagAssignmentTyped : SourceAssignmentHasType function.typedBody locals shape.flagResolution .equal shape.stopRead.node.id :=
      .equal (.intro flagWritable (by rw [shape.flagTargetBare]; exact .nil _) shape.flagTargetType) stopTyped shape.flagAssignmentRequirements
    have flagTyped : StatementHasType function.typedBody ⟨.word,1⟩ locals shape.flagAssignment.id locals ordinary :=
      .assignValue (lookupStatement?_sound shape.flagAssignmentFound) shape.flagAssignmentForm flagAssignmentTyped shape.flagAssignmentType
    have loopTyped := StatementHasType.whileLoop (control:=⟨.word,0⟩)
      (lookupStatement?_sound shape.loopFound) shape.loopForm conditionTyped
      (.cons statementTyped (.singleton flagTyped)) shape.loopType
    have innerReturnTyped := StatementHasType.returnValue (control:=⟨.word,0⟩)
      (lookupStatement?_sound shape.innerReturnFound) shape.innerReturnForm finalTyped shape.innerReturnType
    have expressionTyped : ExpressionHasType function.typedBody lexical shape.expression.id closureType := by
      rw [← shape.expressionType]
      refine .intro (lookupExpression?_sound shape.expressionFound)
        (shape.lambda ▸ ExpressionFormHasRawType.lambda (by simpa only [List.map_cons, List.map_nil] using shape.parameterNames)
          (.cons shape.argumentScheme argumentExtended (.cons shape.flagScheme flagExtended (.cons shape.stopScheme stopExtended (.nil _))))
          (.cons initializedTyped (.cons loopTyped (.singleton innerReturnTyped)))
          (by exact ⟨rfl, rfl, .inl ⟨rfl, rfl⟩⟩)) shape.expressionRaw callable (shape.expressionType ▸ callable) ?_
      rw [shape.requirements, shape.coercions, shape.expressionType]
      exact .ordinary (by intro id member; cases member) (.nil _) rfl
    exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.statementFound) shape.returnStatement expressionTyped shape.statementType)⟩

def observeRelay (function : CheckedFunction) (signature identity : ProgramFunctionSignature) : IO (RelayShape function signature identity) := do
  let [binder] := function.typedBody.inputs | throw (IO.userError "relay inputs")
  let [.expression readNode, .expression calleeNode, .expression initialNode, .statement initialized,
      .expression finalNode, .statement statement] := function.typedBody.nodes | throw (IO.userError "relay nodes")
  let .letDecl localBinder _ := initialized.form | throw (IO.userError "relay local")
  let initialRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody binder readNode .word
  let initial ← Tests.SourceCoreRecursiveIndex.observeDirect function.typedBody identity initialRead.node.id calleeNode initialNode .word .word
  let finalRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody localBinder finalNode .word
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "RelayShape parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "RelayShape inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.word]) "RelayShape returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [binder]) "RelayShape inputs"
  let ⟨binderRequirements⟩ ← observed (binder.schemeRequirements = []) "RelayShape binderRequirements"
  let ⟨localScheme⟩ ← observed (localBinder.scheme = .mono .word) "RelayShape localScheme"
  let ⟨localRequirements⟩ ← observed (localBinder.schemeRequirements = []) "RelayShape localRequirements"
  let ⟨localOwner⟩ ← observed (localBinder.id.owner = function.typedBody.owner) "RelayShape localOwner"
  let ⟨localDistinct⟩ ← observed (localBinder.id ≠ binder.id) "RelayShape localDistinct"
  let ⟨localOrdinary⟩ ← observed (localBinder.comptime = false) "RelayShape localOrdinary"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement initialized.id, .statement statement.id]) "RelayShape roots"
  let ⟨initializedFound⟩ ← observed (function.typedBody.lookupStatement? initialized.id = some initialized) "RelayShape initializedFound"
  let ⟨initializedForm⟩ ← observed (initialized.form = .letDecl localBinder (some initial.value.node.id)) "RelayShape initializedForm"
  let ⟨initializedType⟩ ← observed (initialized.type = .unit) "RelayShape initializedType"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "RelayShape statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some finalRead.node.id)) "RelayShape statementForm"
  let ⟨statementType⟩ ← observed (statement.type = .word) "RelayShape statementType"
  return {binder, localBinder, initialRead, initial, finalRead, initialized, statement, parameters, inputTypes, returns, inputs, binderRequirements, localScheme, localRequirements, localOwner, localDistinct, localOrdinary, roots, initializedFound, initializedForm, initializedType, statementFound, statementForm, statementType}

def observeFactory (function : CheckedFunction) (signature identity relay : ProgramFunctionSignature) : IO (FactoryShape function signature identity relay) := do
  let [binder] := function.typedBody.inputs | throw (IO.userError "factory inputs")
  let [.expression initialReadNode, .expression initialCallee, .expression initialNode, .statement initialized,
      .expression conditionNode, .expression argumentNode, .expression updateCallee, .expression updateNode,
      .statement assignment, .expression stopNode, .statement flagAssignment, .statement loop,
      .expression previousNode, .expression finalCallee, .expression finalNode, .statement innerReturn,
      .expression expression, .statement statement] := function.typedBody.nodes | throw (IO.userError "factory nodes")
  let .lambda [argument, flag, stop] _ _ := expression.form | throw (IO.userError "factory parameters")
  let .letDecl previous _ := initialized.form | throw (IO.userError "factory previous")
  let .assignValue resolution .equal _ := assignment.form | throw (IO.userError "factory assignment")
  let .assignValue flagResolution .equal _ := flagAssignment.form | throw (IO.userError "factory flag assignment")
  let initialRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody binder initialReadNode .word
  let initial ← Tests.SourceCoreRecursiveIndex.observeDirect function.typedBody relay initialRead.node.id initialCallee initialNode .word .word
  let conditionRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody flag conditionNode .bool
  let argumentRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody argument argumentNode .word
  let updated ← Tests.SourceCoreRecursiveIndex.observeDirect function.typedBody relay argumentRead.node.id updateCallee updateNode .word .word
  let stopRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody stop stopNode .bool
  let previousRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody previous previousNode .word
  let final ← Tests.SourceCoreRecursiveIndex.observeDirect function.typedBody identity previousRead.node.id finalCallee finalNode .word .word
  let ⟨argumentScheme⟩ ← observed (argument.scheme = .mono .word) "FactoryShape argumentScheme"
  let ⟨argumentRequirements⟩ ← observed (argument.schemeRequirements = []) "FactoryShape argumentRequirements"
  let ⟨argumentOwner⟩ ← observed (argument.id.owner = function.typedBody.owner) "FactoryShape argumentOwner"
  let ⟨argumentOrdinary⟩ ← observed (argument.comptime = false) "FactoryShape argumentOrdinary"
  let ⟨argumentDistinct⟩ ← observed (argument.id ≠ binder.id) "FactoryShape argumentDistinct"
  let ⟨flagScheme⟩ ← observed (flag.scheme = .mono .bool) "FactoryShape flagScheme"
  let ⟨flagRequirements⟩ ← observed (flag.schemeRequirements = []) "FactoryShape flagRequirements"
  let ⟨flagOwner⟩ ← observed (flag.id.owner = function.typedBody.owner) "FactoryShape flagOwner"
  let ⟨flagOrdinary⟩ ← observed (flag.comptime = false) "FactoryShape flagOrdinary"
  let ⟨flagDistinct⟩ ← observed (flag.id ≠ binder.id) "FactoryShape flagDistinct"
  let ⟨flagArgument⟩ ← observed (flag.id ≠ argument.id) "FactoryShape flagArgument"
  let ⟨stopScheme⟩ ← observed (stop.scheme = .mono .bool) "FactoryShape stopScheme"
  let ⟨stopRequirements⟩ ← observed (stop.schemeRequirements = []) "FactoryShape stopRequirements"
  let ⟨stopOwner⟩ ← observed (stop.id.owner = function.typedBody.owner) "FactoryShape stopOwner"
  let ⟨stopOrdinary⟩ ← observed (stop.comptime = false) "FactoryShape stopOrdinary"
  let ⟨stopDistinct⟩ ← observed (stop.id ≠ binder.id) "FactoryShape stopDistinct"
  let ⟨stopArgument⟩ ← observed (stop.id ≠ argument.id) "FactoryShape stopArgument"
  let ⟨stopFlag⟩ ← observed (stop.id ≠ flag.id) "FactoryShape stopFlag"
  let ⟨previousScheme⟩ ← observed (previous.scheme = .mono .word) "FactoryShape previousScheme"
  let ⟨previousRequirements⟩ ← observed (previous.schemeRequirements = []) "FactoryShape previousRequirements"
  let ⟨previousOwner⟩ ← observed (previous.id.owner = function.typedBody.owner) "FactoryShape previousOwner"
  let ⟨previousOrdinary⟩ ← observed (previous.comptime = false) "FactoryShape previousOrdinary"
  let ⟨previousDistinct⟩ ← observed (previous.id ≠ binder.id) "FactoryShape previousDistinct"
  let ⟨previousArgument⟩ ← observed (previous.id ≠ argument.id) "FactoryShape previousArgument"
  let ⟨previousFlag⟩ ← observed (previous.id ≠ flag.id) "FactoryShape previousFlag"
  let ⟨previousStop⟩ ← observed (previous.id ≠ stop.id) "FactoryShape previousStop"
  let ⟨parameterNames⟩ ← observed ([argument.name, flag.name, stop.name].Nodup) "FactoryShape parameterNames"
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "FactoryShape parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "FactoryShape inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [closureType]) "FactoryShape returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [binder]) "FactoryShape inputs"
  let ⟨binderOwner⟩ ← observed (binder.id.owner = function.typedBody.owner) "FactoryShape binderOwner"
  let ⟨binderRequirements⟩ ← observed (binder.schemeRequirements = []) "FactoryShape binderRequirements"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "FactoryShape roots"
  let ⟨initializedFound⟩ ← observed (function.typedBody.lookupStatement? initialized.id = some initialized) "FactoryShape initializedFound"
  let ⟨initializedForm⟩ ← observed (initialized.form = .letDecl previous (some initial.value.node.id)) "FactoryShape initializedForm"
  let ⟨initializedType⟩ ← observed (initialized.type = .unit) "FactoryShape initializedType"
  let ⟨assignmentFound⟩ ← observed (function.typedBody.lookupStatement? assignment.id = some assignment) "FactoryShape assignmentFound"
  let ⟨assignmentForm⟩ ← observed (assignment.form = .assignValue resolution .equal updated.value.node.id) "FactoryShape assignmentForm"
  let ⟨assignmentType⟩ ← observed (assignment.type = .unit) "FactoryShape assignmentType"
  let ⟨targetRoot⟩ ← observed (resolution.target.root = binder.id) "FactoryShape targetRoot"
  let ⟨targetType⟩ ← observed (resolution.target.type = .word) "FactoryShape targetType"
  let ⟨targetBare⟩ ← observed (resolution.target.projections = []) "FactoryShape targetBare"
  let ⟨assignmentRequirements⟩ ← observed (resolution.requirements = []) "FactoryShape assignmentRequirements"
  let ⟨flagAssignmentFound⟩ ← observed (function.typedBody.lookupStatement? flagAssignment.id = some flagAssignment) "FactoryShape flagAssignmentFound"
  let ⟨flagAssignmentForm⟩ ← observed (flagAssignment.form = .assignValue flagResolution .equal stopRead.node.id) "FactoryShape flagAssignmentForm"
  let ⟨flagAssignmentType⟩ ← observed (flagAssignment.type = .unit) "FactoryShape flagAssignmentType"
  let ⟨flagTargetRoot⟩ ← observed (flagResolution.target.root = flag.id) "FactoryShape flagTargetRoot"
  let ⟨flagTargetType⟩ ← observed (flagResolution.target.type = .bool) "FactoryShape flagTargetType"
  let ⟨flagTargetBare⟩ ← observed (flagResolution.target.projections = []) "FactoryShape flagTargetBare"
  let ⟨flagAssignmentRequirements⟩ ← observed (flagResolution.requirements = []) "FactoryShape flagAssignmentRequirements"
  let ⟨loopFound⟩ ← observed (function.typedBody.lookupStatement? loop.id = some loop) "FactoryShape loopFound"
  let ⟨loopForm⟩ ← observed (loop.form = .whileLoop conditionRead.node.id [assignment.id, flagAssignment.id]) "FactoryShape loopForm"
  let ⟨loopType⟩ ← observed (loop.type = .unit) "FactoryShape loopType"
  let ⟨innerReturnFound⟩ ← observed (function.typedBody.lookupStatement? innerReturn.id = some innerReturn) "FactoryShape innerReturnFound"
  let ⟨innerReturnForm⟩ ← observed (innerReturn.form = .returnStmt (some final.value.node.id)) "FactoryShape innerReturnForm"
  let ⟨innerReturnType⟩ ← observed (innerReturn.type = .word) "FactoryShape innerReturnType"
  let ⟨expressionFound⟩ ← observed (function.typedBody.lookupExpression? expression.id = some expression) "FactoryShape expressionFound"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "FactoryShape statementFound"
  let ⟨lambda⟩ ← observed (expression.form = .lambda [argument, flag, stop] .word [initialized.id, loop.id, innerReturn.id]) "FactoryShape lambda"
  let ⟨expressionRaw⟩ ← observed (expression.rawType = closureType) "FactoryShape expressionRaw"
  let ⟨expressionType⟩ ← observed (expression.type = closureType) "FactoryShape expressionType"
  let ⟨requirements⟩ ← observed (expression.requirements = []) "FactoryShape requirements"
  let ⟨coercions⟩ ← observed (expression.coercions = []) "FactoryShape coercions"
  let ⟨returnStatement⟩ ← observed (statement.form = .returnStmt (some expression.id)) "FactoryShape returnStatement"
  let ⟨statementType⟩ ← observed (statement.type = closureType) "FactoryShape statementType"
  return {binder, argument, flag, stop, previous, initialRead, initial, conditionRead, argumentRead, updated, stopRead, previousRead, final, initialized, assignment, resolution, flagAssignment, flagResolution, loop, innerReturn, expression, statement, argumentScheme, argumentRequirements, argumentOwner, argumentOrdinary, argumentDistinct, flagScheme, flagRequirements, flagOwner, flagOrdinary, flagDistinct, flagArgument, stopScheme, stopRequirements, stopOwner, stopOrdinary, stopDistinct, stopArgument, stopFlag, previousScheme, previousRequirements, previousOwner, previousOrdinary, previousDistinct, previousArgument, previousFlag, previousStop, parameterNames, parameters, inputTypes, returns, inputs, binderOwner, binderRequirements, roots, initializedFound, initializedForm, initializedType, assignmentFound, assignmentForm, assignmentType, targetRoot, targetType, targetBare, assignmentRequirements, flagAssignmentFound, flagAssignmentForm, flagAssignmentType, flagTargetRoot, flagTargetType, flagTargetBare, flagAssignmentRequirements, loopFound, loopForm, loopType, innerReturnFound, innerReturnForm, innerReturnType, expressionFound, statementFound, lambda, expressionRaw, expressionType, requirements, coercions, returnStatement, statementType}

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function identity(value: Word) returns (Word) { return value; } function relay(value: Word) returns (Word) { let local: Word = identity(value); return local; } function make(seed: Word) returns (function(Word, Bool, Bool) returns (Word)) { return lam(next: Word, flag: Bool, stop: Bool) { let previous: Word = relay(seed); while (flag) { seed = relay(next); flag = stop; } return identity(previous); }; }"}] }

structure CheckedFixture where
  program : CheckedProgram
  checked : checkProgram workspace 1000 = .ok program
  wellFormed : ProgramWellFormed (Program.ofChecked program)
  identityFunction : CheckedFunction
  identitySignature : ProgramFunctionSignature
  relayFunction : CheckedFunction
  relaySignature : ProgramFunctionSignature
  makeFunction : CheckedFunction
  makeSignature : ProgramFunctionSignature
  functions : program.functions = [identityFunction, relayFunction, makeFunction]
  signatures : program.signatures.functions = [identitySignature, relaySignature, makeSignature]
  methods : program.methods = []
  identityDeclaration : identityFunction.declaration = identitySignature.id
  relayDeclaration : relayFunction.declaration = relaySignature.id
  makeDeclaration : makeFunction.declaration = makeSignature.id
  identityRelay : identitySignature.id ≠ relaySignature.id
  identityMake : identitySignature.id ≠ makeSignature.id
  relayMake : relaySignature.id ≠ makeSignature.id
  identityShape : IdentityShape identityFunction identitySignature
  relayShape : RelayShape relayFunction relaySignature identitySignature
  makeShape : FactoryShape makeFunction makeSignature identitySignature relaySignature
  identityNodes : identityFunction.typedBody.nodes = identityShape.nodeList
  relayNodes : relayFunction.typedBody.nodes = relayShape.nodeList
  makeNodes : makeFunction.typedBody.nodes = makeShape.nodeList

def checkedFixture : IO CheckedFixture := do
  match checked : checkProgram workspace 1000 with
  | .error error => throw (IO.userError (reprStr error))
  | .ok program =>
    match functions : program.functions, signatures : program.signatures.functions with
    | [identityFunction, relayFunction, makeFunction], [identitySignature, relaySignature, makeSignature] =>
      let identityShape ← Tests.SourceCoreRecursiveIndex.observeIdentity identityFunction identitySignature .word
      let relayShape ← observeRelay relayFunction relaySignature identitySignature
      let makeShape ← observeFactory makeFunction makeSignature identitySignature relaySignature
      let ⟨methods⟩ ← observed (program.methods = []) "scoped methods"
      let ⟨identityDeclaration⟩ ← observed (identityFunction.declaration = identitySignature.id) "identity declaration"
      let ⟨relayDeclaration⟩ ← observed (relayFunction.declaration = relaySignature.id) "relay declaration"
      let ⟨makeDeclaration⟩ ← observed (makeFunction.declaration = makeSignature.id) "make declaration"
      let ⟨identityRelay⟩ ← observed (identitySignature.id ≠ relaySignature.id) "identityRelay"
      let ⟨identityMake⟩ ← observed (identitySignature.id ≠ makeSignature.id) "identityMake"
      let ⟨relayMake⟩ ← observed (relaySignature.id ≠ makeSignature.id) "relayMake"
      let ⟨identityNodes⟩ ← observed (identityFunction.typedBody.nodes = identityShape.nodeList) "identity nodes"
      let ⟨relayNodes⟩ ← observed (relayFunction.typedBody.nodes = relayShape.nodeList) "relay nodes"
      let ⟨makeNodes⟩ ← observed (makeFunction.typedBody.nodes = makeShape.nodeList) "make nodes"
      let deep : CheckedProgramBodiesHaveStatementTyping program 1000 := {
        functions := by
          intro actual member candidate candidateMember accepted
          have identity := checkFunctionBody_success_declaration accepted
          simp only [functions, List.mem_cons, List.not_mem_nil, or_false] at member
          simp only [signatures, List.mem_cons, List.not_mem_nil, or_false] at candidateMember
          rcases member with rfl | rfl | rfl <;> rcases candidateMember with rfl | rfl | rfl
          · exact identityShape.statementTyping program.signatures (fun _ binders => ⟨binders, .builtin .word⟩)
          · exact False.elim (identityRelay (identityDeclaration.symm.trans identity))
          · exact False.elim (identityMake (identityDeclaration.symm.trans identity))
          · exact False.elim (identityRelay (identity.symm.trans relayDeclaration))
          · exact relayShape.statementTyping program.signatures (by simp [signatures])
          · exact False.elim (relayMake (relayDeclaration.symm.trans identity))
          · exact False.elim (identityMake (identity.symm.trans makeDeclaration))
          · exact False.elim (relayMake (identity.symm.trans makeDeclaration))
          · exact makeShape.statementTyping program.signatures (by simp [signatures]) (by simp [signatures])
        methods := by intro method member; simp only [methods, List.not_mem_nil] at member }
      return {
        program, checked, wellFormed := programWellFormed_ofCheckProgram_statements checked deep
        identityFunction, relayFunction, makeFunction, identitySignature, relaySignature, makeSignature, functions, signatures, methods, identityDeclaration, relayDeclaration, makeDeclaration, identityRelay, identityMake, relayMake, identityShape, relayShape, makeShape, identityNodes, relayNodes, makeNodes }
    | _, _ => throw (IO.userError "scoped declaration count")

end Tests.SourceCoreCanonicalScoped
