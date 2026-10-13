import Solcore.Test.SourceCoreOperatorCallsSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreGenericDirect
open Solcore Frontend SourceInference SourceSemantics
abbrev Read := Tests.SourceCoreNamedBranch.Read
abbrev TypedNode := Tests.SourceCoreOperatorCalls.TypedNode

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

structure ChooseShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  firstParameter : TypeSystem.TypeParameterId
  secondParameter : TypeSystem.TypeParameterId
  different : firstParameter ≠ secondParameter
  firstOwner : firstParameter.owner = signature.id
  secondOwner : secondParameter.owner = signature.id
  first : TypedBinder
  second : TypedBinder
  bindersDifferent : second.id ≠ first.id
  read : Read function.typedBody first (.parameter firstParameter)
  statement : StatementNode
  scheme : signature.scheme = ⟨[firstParameter, secondParameter], [],
    .function (.product (.parameter firstParameter) (.parameter secondParameter)) (.parameter firstParameter)⟩
  inputTypes : signature.parameterTypes = [.parameter firstParameter, .parameter secondParameter]
  returns : signature.returnTypes = [.parameter firstParameter]
  inputs : function.typedBody.inputs = [first, second]
  firstRequirements : first.schemeRequirements = []
  secondRequirements : second.schemeRequirements = []
  roots : function.typedBody.roots = [.statement statement.id]
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some read.node.id)
  statementType : statement.type = .parameter firstParameter

def ChooseShape.nodeList {function signature} (shape : ChooseShape function signature) : List Node :=
  [.expression shape.read.node, .statement shape.statement]

theorem ChooseShape.statementTyping {function signature}
    (shape : ChooseShape function signature) (signatures : ProgramSignatures) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.statement.id] := statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type := .parameter shape.firstParameter, hasValue := true, sawReturn := true, control := .returned}
  refine ⟨BodyFacts.singleton facts, rfl, ?_⟩
  intro lexical extension
  rw [shape.inputs, shape.inputTypes] at extension
  cases extension with
  | cons firstScheme firstExtended rest =>
    cases rest with
    | cons _secondScheme secondExtended rest =>
      cases rest
      have parameters : lexical.typeParameters = [shape.firstParameter, shape.secondParameter] := by
        rw [secondExtended.context_fields.2.2.1, firstExtended.context_fields.2.2.1]
        simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
          Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.scheme]
      have owner : lexical.currentDeclaration = some signature.id := by
        rw [secondExtended.context_fields.2.1, firstExtended.context_fields.2.1]
        rfl
      have binders : TypeParameterBindersWellFormed lexical := by
        simp only [TypeParameterBindersWellFormed, parameters, owner]
        constructor
        · simp [shape.different]
        · intro parameter member
          rcases List.mem_cons.mp member with rfl | member
          · rw [shape.firstOwner]
          · cases List.mem_singleton.mp member
            rw [shape.secondOwner]
      have type : TypeAdmissible lexical (.parameter shape.firstParameter) :=
        ⟨binders, .parameter (by simp [parameters]) (by rw [owner, shape.firstOwner])⟩
      have readTyped := shape.read.typed firstScheme shape.firstRequirements type
        (by cases secondExtended; exact .tail shape.bindersDifferent firstExtended.local_self)
        (by cases secondExtended; exact .tail shape.bindersDifferent firstExtended.local_scheme_requirements_self)
      exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.statementFound)
        shape.statementForm readTyped shape.statementType)⟩

/-- The complete original two-parameter record includes the unused second result parameter. -/
structure DirectCall (source : TypedSource) (signature : ProgramFunctionSignature)
    (firstParameter secondParameter : TypeSystem.TypeParameterId)
    (firstType secondType : TypeSystem.Ty) (firstArgument secondArgument : ExpressionId) where
  callee : TypedNode source (.function (.product firstType secondType) firstType)
  value : TypedNode source firstType
  name : String
  instantiation : Frontend.SourceInference.DeclarationInstantiation
  calleeForm : callee.node.form = .reference name (.declaration instantiation)
  form : value.node.form = .call callee.node.id [firstArgument, secondArgument] (.declaration instantiation)
  different : firstParameter ≠ secondParameter
  scheme : signature.scheme = ⟨[firstParameter, secondParameter], [],
    .function (.product (.parameter firstParameter) (.parameter secondParameter)) (.parameter firstParameter)⟩
  inputs : signature.parameterTypes = [.parameter firstParameter, .parameter secondParameter]
  returns : signature.returnTypes = [.parameter firstParameter]
  exact : instantiation = ⟨signature.id, [(secondParameter, secondType), (firstParameter, firstType)],
    .function (.product firstType secondType) firstType, [], signature.parameterComptime, signature.returnComptime⟩

theorem DirectCall.typed {source signature firstParameter secondParameter firstType secondType firstArgument secondArgument}
    (call : DirectCall source signature firstParameter secondParameter firstType secondType firstArgument secondArgument)
    {context : SourceSemantics.Context} (member : signature ∈ context.signatures.functions)
    (firstFormed : TypeAdmissible context firstType) (secondFormed : TypeAdmissible context secondType)
    (firstTyped : ExpressionHasType source context firstArgument firstType)
    (secondTyped : ExpressionHasType source context secondArgument secondType) :
    ExpressionHasType source context call.value.node.id firstType := by
  have valid : SourceSemantics.DeclarationInstantiation.Admissible context call.instantiation := by
    rw [call.exact]
    refine .intro signature member rfl ?_ ?_ ?_ ?_ rfl rfl
    · refine ⟨by simp [call.scheme, call.different], ?_⟩
      simpa only [ParameterSubstitution.domain, List.map_cons, List.map_nil, call.scheme] using
        List.Perm.swap firstParameter secondParameter []
    · intro parameter replacement contained
      rcases List.mem_cons.mp contained with same | contained
      · cases same; exact secondFormed
      · cases List.mem_singleton.mp contained; exact firstFormed
    · simp [call.scheme, TypeSystem.ParameterSubstitution.apply, TypeSystem.ParameterSubstitution.lookup?, Ne.symm call.different]
    · simp [call.scheme]
  have application : DeclarationApplicationValid context call.instantiation [firstType, secondType] firstType [] := by
    refine .intro member valid ?_ ?_ ?_ ?_ ?_
    · simp [call.exact]
    · simp [call.exact, call.inputs, TypeSystem.ParameterSubstitution.apply, TypeSystem.ParameterSubstitution.lookup?, Ne.symm call.different]
    · simp [call.exact, call.returns, TypeSystem.Ty.productMany, TypeSystem.ParameterSubstitution.apply, TypeSystem.ParameterSubstitution.lookup?, Ne.symm call.different]
    · simp [call.exact, TypeSystem.Ty.productMany]
    · simp [call.exact]
  have callee : DirectDeclarationCalleeValid context source call.callee.node.id call.instantiation :=
    .intro (lookupExpression?_sound call.callee.found) call.calleeForm valid
      (call.callee.type.trans (by rw [call.exact])) call.callee.requirements call.callee.coercions
  have typed : ExpressionHasType source context call.value.node.id call.value.node.type := by
    refine .intro (lookupExpression?_sound call.value.found)
      (call.form ▸ ExpressionFormHasRawType.directCall callee application (.cons firstTyped (.cons secondTyped (.nil _))))
      call.value.raw firstFormed (call.value.type.symm ▸ firstFormed) ?_
    rw [call.value.requirements, call.value.coercions, call.value.type]
    exact .directCall (.intro (.nil _) (.nil _) .nil rfl rfl)
  exact Eq.mp (congrArg (fun type => ExpressionHasType source context call.value.node.id type) call.value.type) typed

structure RootShape (function : CheckedFunction) (signature generic : ProgramFunctionSignature)
    (firstParameter secondParameter : TypeSystem.TypeParameterId) (firstType secondType : TypeSystem.Ty) where
  first : TypedBinder
  second : TypedBinder
  different : second.id ≠ first.id
  firstRead : Read function.typedBody first firstType
  secondRead : Read function.typedBody second secondType
  call : DirectCall function.typedBody generic firstParameter secondParameter firstType secondType firstRead.node.id secondRead.node.id
  statement : StatementNode
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [firstType, secondType]
  returns : signature.returnTypes = [firstType]
  inputs : function.typedBody.inputs = [first, second]
  firstScheme : first.scheme = .mono firstType
  secondScheme : second.scheme = .mono secondType
  firstRequirements : first.schemeRequirements = []
  secondRequirements : second.schemeRequirements = []
  roots : function.typedBody.roots = [.statement statement.id]
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some call.value.node.id)
  statementType : statement.type = firstType

def RootShape.nodeList {function signature generic firstParameter secondParameter firstType secondType}
    (shape : RootShape function signature generic firstParameter secondParameter firstType secondType) : List Node :=
  [.expression shape.firstRead.node, .expression shape.secondRead.node, .expression shape.call.callee.node,
   .expression shape.call.value.node, .statement shape.statement]

theorem RootShape.statementTyping {function signature generic firstParameter secondParameter firstType secondType}
    (shape : RootShape function signature generic firstParameter secondParameter firstType secondType)
    (signatures : ProgramSignatures) (member : generic ∈ signatures.functions)
    (firstBuiltin : ∃ builtin, firstType = .constructor (.builtin builtin))
    (secondBuiltin : ∃ builtin, secondType = .constructor (.builtin builtin)) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.statement.id] := statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type := firstType, hasValue := true, sawReturn := true, control := .returned}
  refine ⟨BodyFacts.singleton facts, rfl, ?_⟩
  intro lexical extension
  rw [shape.inputs, shape.inputTypes] at extension
  cases extension with
  | cons firstScheme firstExtended rest =>
    cases rest with
    | cons secondScheme secondExtended rest =>
      cases rest
      have binders : TypeParameterBindersWellFormed lexical := by
        rw [TypeParameterBindersWellFormed, secondExtended.context_fields.2.2.1, firstExtended.context_fields.2.2.1]
        simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
          Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
      have fields : lexical.signatures = signatures := by
        rw [secondExtended.context_fields.1, firstExtended.context_fields.1]
        rfl
      have firstFormed : TypeAdmissible lexical firstType := by
        obtain ⟨builtin, rfl⟩ := firstBuiltin; exact ⟨binders, .builtin builtin⟩
      have secondFormed : TypeAdmissible lexical secondType := by
        obtain ⟨builtin, rfl⟩ := secondBuiltin; exact ⟨binders, .builtin builtin⟩
      have firstTyped := shape.firstRead.typed firstScheme shape.firstRequirements firstFormed
        (by cases secondExtended; exact .tail shape.different firstExtended.local_self)
        (by cases secondExtended; exact .tail shape.different firstExtended.local_scheme_requirements_self)
      have secondTyped := shape.secondRead.typed secondScheme shape.secondRequirements secondFormed
        secondExtended.local_self secondExtended.local_scheme_requirements_self
      have callTyped := shape.call.typed (fields ▸ member) firstFormed secondFormed firstTyped secondTyped
      exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.statementFound)
        shape.statementForm callTyped shape.statementType)⟩


private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

def observeChoose (function : CheckedFunction) (signature : ProgramFunctionSignature) : IO (ChooseShape function signature) := do
  let [firstParameter, secondParameter] := signature.scheme.parameters | throw (IO.userError "choose parameters")
  let [first, second] := function.typedBody.inputs | throw (IO.userError "choose binders")
  let [.expression node, .statement statement] := function.typedBody.nodes | throw (IO.userError "choose nodes")
  let read ← Tests.SourceCoreNamedBranch.observeRead function.typedBody first node (.parameter firstParameter)
  let ⟨different⟩ ← observed (firstParameter ≠ secondParameter) "choose different"
  let ⟨firstOwner⟩ ← observed (firstParameter.owner = signature.id) "choose firstOwner"
  let ⟨secondOwner⟩ ← observed (secondParameter.owner = signature.id) "choose secondOwner"
  let ⟨bindersDifferent⟩ ← observed (second.id ≠ first.id) "choose bindersDifferent"
  let ⟨scheme⟩ ← observed (signature.scheme = ⟨[firstParameter, secondParameter], [], .function (.product (.parameter firstParameter) (.parameter secondParameter)) (.parameter firstParameter)⟩) "choose scheme"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.parameter firstParameter, .parameter secondParameter]) "choose inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.parameter firstParameter]) "choose returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [first, second]) "choose inputs"
  let ⟨firstRequirements⟩ ← observed (first.schemeRequirements = []) "choose firstRequirements"
  let ⟨secondRequirements⟩ ← observed (second.schemeRequirements = []) "choose secondRequirements"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "choose roots"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "choose statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some read.node.id)) "choose statementForm"
  let ⟨statementType⟩ ← observed (statement.type = .parameter firstParameter) "choose statementType"
  return {firstParameter, secondParameter, first, second, read, statement, different, firstOwner, secondOwner, bindersDifferent, scheme, inputTypes, returns, inputs, firstRequirements, secondRequirements, roots, statementFound, statementForm, statementType}

def observeDirect (source : TypedSource) (signature : ProgramFunctionSignature)
    (firstParameter secondParameter : TypeSystem.TypeParameterId) (firstType secondType : TypeSystem.Ty)
    (firstArgument secondArgument : ExpressionId) (callee value : ExpressionNode) :
    IO (DirectCall source signature firstParameter secondParameter firstType secondType firstArgument secondArgument) := do
  let callee ← Tests.SourceCoreOperatorCalls.observeNode source callee (.function (.product firstType secondType) firstType)
  let value ← Tests.SourceCoreOperatorCalls.observeNode source value firstType
  let .reference name (.declaration instantiation) := callee.node.form | throw (IO.userError "generic direct callee")
  let ⟨calleeForm⟩ ← observed (callee.node.form = .reference name (.declaration instantiation)) "generic direct calleeForm"
  let ⟨form⟩ ← observed (value.node.form = .call callee.node.id [firstArgument, secondArgument] (.declaration instantiation)) "generic direct form"
  let ⟨different⟩ ← observed (firstParameter ≠ secondParameter) "generic direct different"
  let ⟨scheme⟩ ← observed (signature.scheme = ⟨[firstParameter, secondParameter], [], .function (.product (.parameter firstParameter) (.parameter secondParameter)) (.parameter firstParameter)⟩) "generic direct scheme"
  let ⟨inputs⟩ ← observed (signature.parameterTypes = [.parameter firstParameter, .parameter secondParameter]) "generic direct inputs"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.parameter firstParameter]) "generic direct returns"
  let ⟨exact⟩ ← observed (instantiation = ⟨signature.id, [(secondParameter, secondType), (firstParameter, firstType)], .function (.product firstType secondType) firstType, [], signature.parameterComptime, signature.returnComptime⟩) "generic direct exact"
  return {callee, value, name, instantiation, calleeForm, form, different, scheme, inputs, returns, exact}

def observeRoot (function : CheckedFunction) (signature generic : ProgramFunctionSignature)
    (firstParameter secondParameter : TypeSystem.TypeParameterId) (firstType secondType : TypeSystem.Ty) :
    IO (RootShape function signature generic firstParameter secondParameter firstType secondType) := do
  let [first, second] := function.typedBody.inputs | throw (IO.userError "root inputs")
  let [.expression readFirst, .expression readSecond, .expression callee, .expression value, .statement statement] := function.typedBody.nodes
    | throw (IO.userError "root nodes")
  let firstRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody first readFirst firstType
  let secondRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody second readSecond secondType
  let call ← observeDirect function.typedBody generic firstParameter secondParameter firstType secondType firstRead.node.id secondRead.node.id callee value
  let ⟨different⟩ ← observed (second.id ≠ first.id) "generic root different"
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "generic root parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [firstType, secondType]) "generic root inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [firstType]) "generic root returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [first, second]) "generic root inputs"
  let ⟨firstScheme⟩ ← observed (first.scheme = .mono firstType) "generic root firstScheme"
  let ⟨secondScheme⟩ ← observed (second.scheme = .mono secondType) "generic root secondScheme"
  let ⟨firstRequirements⟩ ← observed (first.schemeRequirements = []) "generic root firstRequirements"
  let ⟨secondRequirements⟩ ← observed (second.schemeRequirements = []) "generic root secondRequirements"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "generic root roots"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "generic root statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some call.value.node.id)) "generic root statementForm"
  let ⟨statementType⟩ ← observed (statement.type = firstType) "generic root statementType"
  return {first, second, firstRead, secondRead, call, statement, different, parameters, inputTypes, returns, inputs, firstScheme, secondScheme, firstRequirements, secondRequirements, roots, statementFound, statementForm, statementType}

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function choose<A, B>(a: A, b: B) returns (A) { return a; }",
    "function wordRoot(value: Word, flag: Bool) returns (Word) { return choose(value, flag); }",
    "function boolRoot(flag: Bool, value: Word) returns (Bool) { return choose(flag, value); }"]}] }

structure CheckedFixture where
  program : CheckedProgram
  checked : checkProgram workspace 1000 = .ok program
  wellFormed : ProgramWellFormed (Program.ofChecked program)
  chooseFunction : CheckedFunction
  wordFunction : CheckedFunction
  boolFunction : CheckedFunction
  chooseSignature : ProgramFunctionSignature
  wordSignature : ProgramFunctionSignature
  boolSignature : ProgramFunctionSignature
  functions : program.functions = [chooseFunction, wordFunction, boolFunction]
  signatures : program.signatures.functions = [chooseSignature, wordSignature, boolSignature]
  methods : program.methods = []
  chooseDeclaration : chooseFunction.declaration = chooseSignature.id
  wordDeclaration : wordFunction.declaration = wordSignature.id
  boolDeclaration : boolFunction.declaration = boolSignature.id
  chooseWord : chooseSignature.id ≠ wordSignature.id
  chooseBool : chooseSignature.id ≠ boolSignature.id
  wordBool : wordSignature.id ≠ boolSignature.id
  chooseShape : ChooseShape chooseFunction chooseSignature
  wordShape : RootShape wordFunction wordSignature chooseSignature chooseShape.firstParameter chooseShape.secondParameter .word .bool
  boolShape : RootShape boolFunction boolSignature chooseSignature chooseShape.firstParameter chooseShape.secondParameter .bool .word
  chooseNodes : chooseFunction.typedBody.nodes = chooseShape.nodeList
  wordNodes : wordFunction.typedBody.nodes = wordShape.nodeList
  boolNodes : boolFunction.typedBody.nodes = boolShape.nodeList

def checkedFixture : IO CheckedFixture := do
  match checked : checkProgram workspace 1000 with
  | .error error => throw (IO.userError (reprStr error))
  | .ok program =>
    match functions : program.functions, signatures : program.signatures.functions with
    | [chooseFunction, wordFunction, boolFunction], [chooseSignature, wordSignature, boolSignature] =>
      let chooseShape ← observeChoose chooseFunction chooseSignature
      let wordShape ← observeRoot wordFunction wordSignature chooseSignature chooseShape.firstParameter chooseShape.secondParameter .word .bool
      let boolShape ← observeRoot boolFunction boolSignature chooseSignature chooseShape.firstParameter chooseShape.secondParameter .bool .word
      let ⟨methods⟩ ← observed (program.methods = []) "generic fixture methods"
      let ⟨chooseDeclaration⟩ ← observed (chooseFunction.declaration = chooseSignature.id) "generic fixture chooseDeclaration"
      let ⟨wordDeclaration⟩ ← observed (wordFunction.declaration = wordSignature.id) "generic fixture wordDeclaration"
      let ⟨boolDeclaration⟩ ← observed (boolFunction.declaration = boolSignature.id) "generic fixture boolDeclaration"
      let ⟨chooseWord⟩ ← observed (chooseSignature.id ≠ wordSignature.id) "generic fixture chooseWord"
      let ⟨chooseBool⟩ ← observed (chooseSignature.id ≠ boolSignature.id) "generic fixture chooseBool"
      let ⟨wordBool⟩ ← observed (wordSignature.id ≠ boolSignature.id) "generic fixture wordBool"
      let ⟨chooseNodes⟩ ← observed (chooseFunction.typedBody.nodes = chooseShape.nodeList) "generic fixture chooseNodes"
      let ⟨wordNodes⟩ ← observed (wordFunction.typedBody.nodes = wordShape.nodeList) "generic fixture wordNodes"
      let ⟨boolNodes⟩ ← observed (boolFunction.typedBody.nodes = boolShape.nodeList) "generic fixture boolNodes"
      let deep : CheckedProgramBodiesHaveStatementTyping program 1000 := {
        functions := by
          intro actual member candidate candidateMember accepted
          have identity := checkFunctionBody_success_declaration accepted
          simp only [functions, List.mem_cons, List.not_mem_nil, or_false] at member
          simp only [signatures, List.mem_cons, List.not_mem_nil, or_false] at candidateMember
          rcases member with rfl | rfl | rfl <;> rcases candidateMember with rfl | rfl | rfl
          · exact chooseShape.statementTyping program.signatures
          · exact False.elim (chooseWord (chooseDeclaration.symm.trans identity))
          · exact False.elim (chooseBool (chooseDeclaration.symm.trans identity))
          · exact False.elim (chooseWord (identity.symm.trans wordDeclaration))
          · exact wordShape.statementTyping program.signatures (by simp [signatures]) ⟨.word, rfl⟩ ⟨.bool, rfl⟩
          · exact False.elim (wordBool (wordDeclaration.symm.trans identity))
          · exact False.elim (chooseBool (identity.symm.trans boolDeclaration))
          · exact False.elim (wordBool (identity.symm.trans boolDeclaration))
          · exact boolShape.statementTyping program.signatures (by simp [signatures]) ⟨.bool, rfl⟩ ⟨.word, rfl⟩
        methods := by intro method member; simp only [methods, List.not_mem_nil] at member }
      return {program, checked, wellFormed := programWellFormed_ofCheckProgram_statements checked deep, chooseFunction, wordFunction, boolFunction, chooseSignature, wordSignature, boolSignature, functions, signatures, methods, chooseDeclaration, wordDeclaration, boolDeclaration, chooseWord, chooseBool, wordBool, chooseShape, wordShape, boolShape, chooseNodes, wordNodes, boolNodes}
    | _, _ => throw (IO.userError "generic direct declarations")
end Tests.SourceCoreGenericDirect
