import Solcore.SourceSemantics.SourceProgramCheckingSoundness
set_option autoImplicit false
set_option Elab.async false
/-! Independent Source typing for a factory that initializes a fresh lexical
local from its parameter and returns a closure capturing that local cell. -/
namespace Tests.SourceCoreCapturedLocal
open Solcore Frontend SourceInference SourceSemantics

structure FactoryShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  binder : TypedBinder
  localBinder : TypedBinder
  localScheme : localBinder.scheme = .mono .word
  localRequirements : localBinder.schemeRequirements = []
  localOrdinary : localBinder.comptime = false
  localOwner : localBinder.id.owner = function.typedBody.owner
  localDistinct : localBinder.id ≠ binder.id
  initialRead : ExpressionNode
  initialized : StatementNode
  read : ExpressionNode
  innerReturn : StatementNode
  expression : ExpressionNode
  statement : StatementNode
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [.function .unit .word]
  inputs : function.typedBody.inputs = [binder]
  binderRequirements : binder.schemeRequirements = []
  roots : function.typedBody.roots = [.statement initialized.id, .statement statement.id]
  initialReadFound : function.typedBody.lookupExpression? initialRead.id = some initialRead
  initializedFound : function.typedBody.lookupStatement? initialized.id = some initialized
  initialReadForm : initialRead.form = .reference binder.name (.local binder.id)
  initialReadRaw : initialRead.rawType = .word
  initialReadType : initialRead.type = .word
  initialReadRequirements : initialRead.requirements = []
  initialReadCoercions : initialRead.coercions = []
  initializedForm : initialized.form = .letDecl localBinder (some initialRead.id)
  initializedType : initialized.type = .unit
  readFound : function.typedBody.lookupExpression? read.id = some read
  innerReturnFound : function.typedBody.lookupStatement? innerReturn.id = some innerReturn
  expressionFound : function.typedBody.lookupExpression? expression.id = some expression
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  readForm : read.form = .reference localBinder.name (.local localBinder.id)
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
  have same : statements = [shape.initialized.id, shape.statement.id] :=
    statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {
    type := .function .unit .word
    hasValue := true
    sawReturn := true
    control := .returned }
  let letFacts : StatementFacts := {
    type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit }
  refine ⟨BodyFacts.cons letFacts (BodyFacts.singleton facts), rfl, ?_⟩
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
    let innerContext := lexical.withLocal shape.localBinder.id shape.localBinder.scheme shape.localBinder.schemeRequirements
    have localExtended : BinderExtends function.typedBody.owner lexical shape.localBinder innerContext := by
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
    have callable : TypeAdmissible innerContext (.function .unit .word) :=
      ⟨binders, .function (.builtin .unit) (.builtin .word)⟩
    have innerWord : TypeAdmissible innerContext .word := ⟨binders, .builtin .word⟩
    have initialInstantiation : LocalSchemeInstantiationValid lexical shape.binder .word [] := by
      refine .intro (LocalSchemeRequirementsWellFormed.empty _ _ shape.binderRequirements)
        (scheme.symm ▸ SchemeWellFormed.monoAdmissible word) [] ?_ ?_ ?_ (by simp) ?_ ?_
      · simpa only [scheme, TypeSystem.Scheme.mono] using ExactSubstitution.empty
      · intro metavariable replacement member; cases member
      · simpa only [scheme, TypeSystem.Scheme.mono] using SchemeInstantiates.empty_apply .word
      · intro id member; cases member
      · rw [instantiateLocalSchemePredicates, shape.binderRequirements]
        exact .nil
    have initialReadTyped : ExpressionHasType function.typedBody lexical shape.initialRead.id .word := by
      rw [← shape.initialReadType]
      refine .intro (lookupExpression?_sound shape.initialReadFound)
        (shape.initialReadForm ▸ ExpressionFormHasRawType.reference
          (.local head.local_self head.local_scheme_requirements_self initialInstantiation))
        shape.initialReadRaw word (shape.initialReadType ▸ word) ?_
      rw [shape.initialReadRequirements, shape.initialReadCoercions, shape.initialReadType]
      exact .ordinary (by intro id member; cases member) (.nil _) rfl
    have instantiation : LocalSchemeInstantiationValid innerContext shape.localBinder .word [] := by
      refine .intro (LocalSchemeRequirementsWellFormed.empty _ _ shape.localRequirements)
        (shape.localScheme.symm ▸ SchemeWellFormed.monoAdmissible innerWord) [] ?_ ?_ ?_ (by simp) ?_ ?_
      · simpa only [shape.localScheme, TypeSystem.Scheme.mono] using ExactSubstitution.empty
      · intro metavariable replacement member; cases member
      · simpa only [shape.localScheme, TypeSystem.Scheme.mono] using SchemeInstantiates.empty_apply .word
      · intro id member; cases member
      · rw [instantiateLocalSchemePredicates, shape.localRequirements]
        exact .nil
    have readTyped : ExpressionHasType function.typedBody innerContext shape.read.id .word := by
      rw [← shape.readType]
      refine .intro (lookupExpression?_sound shape.readFound)
        (shape.readForm ▸ ExpressionFormHasRawType.reference
          (.local localExtended.local_self localExtended.local_scheme_requirements_self instantiation))
        shape.readRaw innerWord (shape.readType ▸ innerWord) ?_
      rw [shape.readRequirements, shape.readCoercions, shape.readType]
      exact .ordinary (by intro id member; cases member) (.nil _) rfl
    have expressionTyped : ExpressionHasType function.typedBody innerContext shape.expression.id
        (.function .unit .word) := by
      rw [← shape.expressionType]
      refine .intro (lookupExpression?_sound shape.expressionFound)
        (shape.lambda ▸ ExpressionFormHasRawType.lambda (by simp)
          (.nil _)
          (.singleton (.returnValue (lookupStatement?_sound shape.innerReturnFound)
            shape.innerReturnForm readTyped shape.innerReturnType))
          (by exact ⟨rfl, rfl, .inl ⟨rfl, rfl⟩⟩)) shape.expressionRaw
        callable (shape.expressionType ▸ callable) ?_
      rw [shape.requirements, shape.coercions, shape.expressionType]
      exact .ordinary (by intro id member; cases member) (.nil _) rfl
    have initializedTyped : StatementHasType function.typedBody
        ⟨.function .unit .word, 0⟩ lexical shape.initialized.id innerContext letFacts := by
      apply StatementHasType.letInitialized (lookupStatement?_sound shape.initializedFound) shape.initializedForm
      · simpa only [shape.localScheme, TypeSystem.Scheme.mono] using initialReadTyped
      · rw [shape.localScheme]; rfl
      · rw [shape.localScheme]; rfl
      · exact localExtended
      · exact shape.initializedType
    exact ⟨_, .cons initializedTyped (.singleton (.returnValue (lookupStatement?_sound shape.statementFound)
      shape.returnStatement expressionTyped shape.statementType))⟩

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  externalLibraries := []
  mainSources := [{path := "main.solc", content :=
    "function make(seed: Word) returns (function() returns (Word)) { let local: Word = seed; return lam() { return local; }; }"}] }

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

def observeShape (function : CheckedFunction) (signature : ProgramFunctionSignature) :
    IO (FactoryShape function signature) := do
  let [binder] := function.typedBody.inputs
    | throw (IO.userError "captured factory input shape")
  let [Node.expression initialRead, Node.statement initialized, Node.expression read, Node.statement innerReturn,
      Node.expression expression, Node.statement statement] := function.typedBody.nodes
    | throw (IO.userError "captured factory occurrence shape")
  let .letDecl localBinder _ := initialized.form
    | throw (IO.userError "captured local binder")
  let ⟨localScheme⟩ ← observed (localBinder.scheme = .mono .word) "packed argument scheme"
  let ⟨localRequirements⟩ ← observed (localBinder.schemeRequirements = []) "packed argument requirements"
  let ⟨localOrdinary⟩ ← observed (localBinder.comptime = false) "captured local ordinary binder"
  let ⟨localOwner⟩ ← observed (localBinder.id.owner = function.typedBody.owner) "packed argument owner"
  let ⟨localDistinct⟩ ← observed (localBinder.id ≠ binder.id) "packed argument identity"
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "captured factory parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "captured factory inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.function .unit .word]) "captured factory returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [binder]) "captured factory inputs"
  let ⟨binderRequirements⟩ ← observed (binder.schemeRequirements = []) "captured factory binderRequirements"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement initialized.id, .statement statement.id]) "captured factory roots"
  let ⟨initialReadFound⟩ ← observed (function.typedBody.lookupExpression? initialRead.id = some initialRead) "captured local initialReadFound"
  let ⟨initializedFound⟩ ← observed (function.typedBody.lookupStatement? initialized.id = some initialized) "captured local initializedFound"
  let ⟨initialReadForm⟩ ← observed (initialRead.form = .reference binder.name (.local binder.id)) "captured local initialReadForm"
  let ⟨initialReadRaw⟩ ← observed (initialRead.rawType = .word) "captured local initialReadRaw"
  let ⟨initialReadType⟩ ← observed (initialRead.type = .word) "captured local initialReadType"
  let ⟨initialReadRequirements⟩ ← observed (initialRead.requirements = []) "captured local initialReadRequirements"
  let ⟨initialReadCoercions⟩ ← observed (initialRead.coercions = []) "captured local initialReadCoercions"
  let ⟨initializedForm⟩ ← observed (initialized.form = .letDecl localBinder (some initialRead.id)) "captured local initializedForm"
  let ⟨initializedType⟩ ← observed (initialized.type = .unit) "captured local initializedType"
  let ⟨readFound⟩ ← observed (function.typedBody.lookupExpression? read.id = some read) "captured factory readFound"
  let ⟨innerReturnFound⟩ ← observed (function.typedBody.lookupStatement? innerReturn.id = some innerReturn) "captured factory innerReturnFound"
  let ⟨expressionFound⟩ ← observed (function.typedBody.lookupExpression? expression.id = some expression) "captured factory expressionFound"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "captured factory statementFound"
  let ⟨readForm⟩ ← observed (read.form = .reference localBinder.name (.local localBinder.id)) "captured factory readForm"
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
  return { binder, localBinder, localScheme, localRequirements, localOrdinary, localOwner, localDistinct, initialRead, initialized, initialReadFound, initializedFound, initialReadForm, initialReadRaw, initialReadType, initialReadRequirements, initialReadCoercions, initializedForm, initializedType, read, innerReturn, expression, statement, parameters, inputTypes, returns, inputs, binderRequirements, roots, readFound, innerReturnFound, expressionFound, statementFound, readForm, readRaw, readType, readRequirements, readCoercions, innerReturnForm, innerReturnType, lambda, expressionRaw, expressionType, requirements, coercions, returnStatement, statementType }

structure CheckedFixture where
  program : CheckedProgram
  checked : checkProgram workspace 1000 = .ok program
  wellFormed : ProgramWellFormed (Program.ofChecked program)
  function : CheckedFunction
  signature : ProgramFunctionSignature
  functions : program.functions = [function]
  signatures : program.signatures.functions = [signature]
  methods : program.methods = []
  sourceShape : FactoryShape function signature
  nodes : function.typedBody.nodes = [.expression sourceShape.initialRead, .statement sourceShape.initialized, .expression sourceShape.read,
    .statement sourceShape.innerReturn, .expression sourceShape.expression, .statement sourceShape.statement]

def checkedFixture : IO CheckedFixture := do
  match checked : checkProgram workspace 1000 with
  | .error error => throw (IO.userError (reprStr error))
  | .ok program =>
    match functions : program.functions, signatures : program.signatures.functions with
    | [function], [signature] =>
      let sourceShape ← observeShape function signature
      if methods : program.methods = [] then
        let deep : CheckedProgramBodiesHaveStatementTyping program 1000 := {
          functions := by
            intro actual member candidate candidateMember _accepted
            have sameFunction : actual = function := by simpa only [functions, List.mem_singleton] using member
            have sameSignature : candidate = signature := by simpa only [signatures, List.mem_singleton] using candidateMember
            subst actual candidate
            exact sourceShape.statementTyping program.signatures
          methods := by intro method member; simp only [methods, List.not_mem_nil] at member }
        if nodes : function.typedBody.nodes = [.expression sourceShape.initialRead, .statement sourceShape.initialized, .expression sourceShape.read,
            .statement sourceShape.innerReturn, .expression sourceShape.expression, .statement sourceShape.statement] then
          return ⟨program, checked, programWellFormed_ofCheckProgram_statements checked deep,
            function, signature, functions, signatures, methods, sourceShape, nodes⟩
        else throw (IO.userError "captured factory complete node graph changed")
      else throw (IO.userError "unexpected captured factory methods")
    | _, _ => throw (IO.userError "captured factory declaration count")

end Tests.SourceCoreCapturedLocal
