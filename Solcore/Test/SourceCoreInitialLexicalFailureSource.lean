import Solcore.SourceSemantics.SourceProgramCheckingSoundness
set_option autoImplicit false
set_option Elab.async false
/-! Independent Source typing of a real uninitialized local read and a
subsequent identity call. Runtime failure is established separately. -/
namespace Tests.SourceCoreInitialLexicalFailure
open Solcore Frontend SourceInference SourceSemantics

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

structure FailedShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  binder : TypedBinder
  declared : StatementNode
  read : ExpressionNode
  statement : StatementNode
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = []
  returns : signature.returnTypes = [.word]
  inputs : function.typedBody.inputs = []
  binderScheme : binder.scheme = .mono .word
  binderRequirements : binder.schemeRequirements = []
  binderOrdinary : binder.comptime = false
  binderOwner : binder.id.owner = function.typedBody.owner
  roots : function.typedBody.roots = [.statement declared.id, .statement statement.id]
  nodes : function.typedBody.nodes = [.statement declared, .expression read, .statement statement]
  declaredFound : function.typedBody.lookupStatement? declared.id = some declared
  declaredForm : declared.form = .letDecl binder none
  declaredType : declared.type = .unit
  readFound : function.typedBody.lookupExpression? read.id = some read
  readForm : read.form = .reference binder.name (.local binder.id)
  readRaw : read.rawType = .word
  readType : read.type = .word
  readRequirements : read.requirements = []
  readCoercions : read.coercions = []
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some read.id)
  statementType : statement.type = .word

theorem FailedShape.statementTyping {function : CheckedFunction} {signature : ProgramFunctionSignature}
    (shape : FailedShape function signature) (signatures : ProgramSignatures) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.declared.id, shape.statement.id] :=
    statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type := .word, hasValue := true, sawReturn := true, control := .returned}
  let letFacts : StatementFacts := {type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit}
  refine ⟨BodyFacts.cons letFacts (BodyFacts.singleton facts), rfl, ?_⟩
  intro lexical extension
  rw [shape.inputs, shape.inputTypes] at extension
  cases extension
  let lexical := checkedBodyContext signatures signature function
  have binders : TypeParameterBindersWellFormed lexical := by
    simp [TypeParameterBindersWellFormed, lexical, checkedBodyContext, declarationContext, Context.ofSignatures,
      Context.forDeclaration, Context.withAssumptions, Context.withSolvedRequirements,
      Context.withResidualTypeVariables, shape.parameters]
  have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
  let inner := lexical.withLocal shape.binder.id shape.binder.scheme shape.binder.schemeRequirements
  have extended : BinderExtends function.typedBody.owner lexical shape.binder inner := by
    apply BinderExtends.intro
    · exact {
        owned := shape.binderOwner
        scheme := shape.binderScheme.symm ▸ SchemeWellFormed.monoAdmissible word
        quantified_fresh := by rw [shape.binderScheme]; simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]
        monomorphic_requirements_empty := fun _ => shape.binderRequirements }
    · simp [LocalFresh, lexical, checkedBodyContext, declarationContext, Context.ofSignatures,
        Context.forDeclaration, Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables]
  have innerWord : TypeAdmissible inner .word := ⟨binders, .builtin .word⟩
  have instantiation : LocalSchemeInstantiationValid inner shape.binder .word [] := by
    refine .intro (LocalSchemeRequirementsWellFormed.empty _ _ shape.binderRequirements)
      (shape.binderScheme.symm ▸ SchemeWellFormed.monoAdmissible innerWord) [] ?_ ?_ ?_ (by simp) ?_ ?_
    · simpa only [shape.binderScheme, TypeSystem.Scheme.mono] using ExactSubstitution.empty
    · intro metavariable replacement member; cases member
    · simpa only [shape.binderScheme, TypeSystem.Scheme.mono] using SchemeInstantiates.empty_apply .word
    · intro id member; cases member
    · rw [instantiateLocalSchemePredicates, shape.binderRequirements]; exact .nil
  have readTyped : ExpressionHasType function.typedBody inner shape.read.id .word := by
    rw [← shape.readType]
    refine .intro (lookupExpression?_sound shape.readFound)
      (shape.readForm ▸ ExpressionFormHasRawType.reference
        (.local extended.local_self extended.local_scheme_requirements_self instantiation))
      shape.readRaw innerWord (shape.readType ▸ innerWord) ?_
    rw [shape.readRequirements, shape.readCoercions, shape.readType]
    exact .ordinary (by intro id member; cases member) (.nil _) rfl
  have declared : StatementHasType function.typedBody ⟨.word, 0⟩ lexical shape.declared.id inner letFacts := by
    apply StatementHasType.letUninitialized (lookupStatement?_sound shape.declaredFound) shape.declaredForm
    · rw [shape.binderScheme]; rfl
    · rw [shape.binderScheme]; rfl
    · exact extended
    · exact shape.declaredType
  exact ⟨_, .cons declared (.singleton (.returnValue (lookupStatement?_sound shape.statementFound)
    shape.statementForm readTyped shape.statementType))⟩

structure IdentityShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  binder : TypedBinder
  read : ExpressionNode
  statement : StatementNode
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [.word]
  inputs : function.typedBody.inputs = [binder]
  binderScheme : binder.scheme = .mono .word
  binderRequirements : binder.schemeRequirements = []
  binderOrdinary : binder.comptime = false
  roots : function.typedBody.roots = [.statement statement.id]
  nodes : function.typedBody.nodes = [.expression read, .statement statement]
  readFound : function.typedBody.lookupExpression? read.id = some read
  readForm : read.form = .reference binder.name (.local binder.id)
  readRaw : read.rawType = .word
  readType : read.type = .word
  readRequirements : read.requirements = []
  readCoercions : read.coercions = []
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some read.id)
  statementType : statement.type = .word

theorem IdentityShape.statementTyping {function : CheckedFunction} {signature : ProgramFunctionSignature}
    (shape : IdentityShape function signature) (signatures : ProgramSignatures) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.statement.id] := statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type := .word, hasValue := true, sawReturn := true, control := .returned}
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
    have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
    have instantiation : LocalSchemeInstantiationValid lexical shape.binder .word [] := by
      refine .intro (LocalSchemeRequirementsWellFormed.empty _ _ shape.binderRequirements)
        (scheme.symm ▸ SchemeWellFormed.monoAdmissible word) [] ?_ ?_ ?_ (by simp) ?_ ?_
      · simpa only [scheme, TypeSystem.Scheme.mono] using ExactSubstitution.empty
      · intro metavariable replacement member; cases member
      · simpa only [scheme, TypeSystem.Scheme.mono] using SchemeInstantiates.empty_apply .word
      · intro id member; cases member
      · rw [instantiateLocalSchemePredicates, shape.binderRequirements]; exact .nil
    have readTyped : ExpressionHasType function.typedBody lexical shape.read.id .word := by
      rw [← shape.readType]
      refine .intro (lookupExpression?_sound shape.readFound)
        (shape.readForm ▸ ExpressionFormHasRawType.reference
          (.local head.local_self head.local_scheme_requirements_self instantiation))
        shape.readRaw word (shape.readType ▸ word) ?_
      rw [shape.readRequirements, shape.readCoercions, shape.readType]
      exact .ordinary (by intro id member; cases member) (.nil _) rfl
    exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.statementFound)
      shape.statementForm readTyped shape.statementType)⟩

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function failed() returns (Word) { let local: Word; return local; } function identity(seed: Word) returns (Word) { return seed; }"}] }

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

def observeFailed (function : CheckedFunction) (signature : ProgramFunctionSignature) : IO (FailedShape function signature) := do
  let [Node.statement declared, Node.expression read, Node.statement statement] := function.typedBody.nodes
    | throw (IO.userError "failed occurrence shape")
  let .letDecl binder none := declared.form | throw (IO.userError "failed uninitialized binder")
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "observeFailed parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = []) "observeFailed inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.word]) "observeFailed returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = []) "observeFailed inputs"
  let ⟨binderScheme⟩ ← observed (binder.scheme = .mono .word) "observeFailed binderScheme"
  let ⟨binderRequirements⟩ ← observed (binder.schemeRequirements = []) "observeFailed binderRequirements"
  let ⟨binderOrdinary⟩ ← observed (binder.comptime = false) "observeFailed binderOrdinary"
  let ⟨binderOwner⟩ ← observed (binder.id.owner = function.typedBody.owner) "observeFailed binderOwner"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement declared.id, .statement statement.id]) "observeFailed roots"
  let ⟨nodes⟩ ← observed (function.typedBody.nodes = [.statement declared, .expression read, .statement statement]) "observeFailed nodes"
  let ⟨declaredFound⟩ ← observed (function.typedBody.lookupStatement? declared.id = some declared) "observeFailed declaredFound"
  let ⟨declaredForm⟩ ← observed (declared.form = .letDecl binder none) "observeFailed declaredForm"
  let ⟨declaredType⟩ ← observed (declared.type = .unit) "observeFailed declaredType"
  let ⟨readFound⟩ ← observed (function.typedBody.lookupExpression? read.id = some read) "observeFailed readFound"
  let ⟨readForm⟩ ← observed (read.form = .reference binder.name (.local binder.id)) "observeFailed readForm"
  let ⟨readRaw⟩ ← observed (read.rawType = .word) "observeFailed readRaw"
  let ⟨readType⟩ ← observed (read.type = .word) "observeFailed readType"
  let ⟨readRequirements⟩ ← observed (read.requirements = []) "observeFailed readRequirements"
  let ⟨readCoercions⟩ ← observed (read.coercions = []) "observeFailed readCoercions"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "observeFailed statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some read.id)) "observeFailed statementForm"
  let ⟨statementType⟩ ← observed (statement.type = .word) "observeFailed statementType"
  return {binder, declared, read, statement, parameters, inputTypes, returns, inputs, binderScheme, binderRequirements, binderOrdinary, binderOwner, roots, nodes, declaredFound, declaredForm, declaredType, readFound, readForm, readRaw, readType, readRequirements, readCoercions, statementFound, statementForm, statementType}

def observeIdentity (function : CheckedFunction) (signature : ProgramFunctionSignature) : IO (IdentityShape function signature) := do
  let [binder] := function.typedBody.inputs | throw (IO.userError "identity input")
  let [Node.expression read, Node.statement statement] := function.typedBody.nodes
    | throw (IO.userError "identity occurrence shape")
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "observeIdentity parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "observeIdentity inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.word]) "observeIdentity returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [binder]) "observeIdentity inputs"
  let ⟨binderScheme⟩ ← observed (binder.scheme = .mono .word) "observeIdentity binderScheme"
  let ⟨binderRequirements⟩ ← observed (binder.schemeRequirements = []) "observeIdentity binderRequirements"
  let ⟨binderOrdinary⟩ ← observed (binder.comptime = false) "observeIdentity binderOrdinary"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "observeIdentity roots"
  let ⟨nodes⟩ ← observed (function.typedBody.nodes = [.expression read, .statement statement]) "observeIdentity nodes"
  let ⟨readFound⟩ ← observed (function.typedBody.lookupExpression? read.id = some read) "observeIdentity readFound"
  let ⟨readForm⟩ ← observed (read.form = .reference binder.name (.local binder.id)) "observeIdentity readForm"
  let ⟨readRaw⟩ ← observed (read.rawType = .word) "observeIdentity readRaw"
  let ⟨readType⟩ ← observed (read.type = .word) "observeIdentity readType"
  let ⟨readRequirements⟩ ← observed (read.requirements = []) "observeIdentity readRequirements"
  let ⟨readCoercions⟩ ← observed (read.coercions = []) "observeIdentity readCoercions"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "observeIdentity statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some read.id)) "observeIdentity statementForm"
  let ⟨statementType⟩ ← observed (statement.type = .word) "observeIdentity statementType"
  return {binder, read, statement, parameters, inputTypes, returns, inputs, binderScheme, binderRequirements, binderOrdinary, roots, nodes, readFound, readForm, readRaw, readType, readRequirements, readCoercions, statementFound, statementForm, statementType}

structure CheckedFixture where
  program : CheckedProgram
  checked : checkProgram workspace 1000 = .ok program
  wellFormed : ProgramWellFormed (Program.ofChecked program)
  failedFunction : CheckedFunction
  identityFunction : CheckedFunction
  failedSignature : ProgramFunctionSignature
  identitySignature : ProgramFunctionSignature
  functions : program.functions = [failedFunction, identityFunction]
  signatures : program.signatures.functions = [failedSignature, identitySignature]
  methods : program.methods = []
  failedDeclaration : failedFunction.declaration = failedSignature.id
  identityDeclaration : identityFunction.declaration = identitySignature.id
  distinct : failedSignature.id ≠ identitySignature.id
  failedShape : FailedShape failedFunction failedSignature
  identityShape : IdentityShape identityFunction identitySignature

def checkedFixture : IO CheckedFixture := do
  match checked : checkProgram workspace 1000 with
  | .error error => throw (IO.userError (reprStr error))
  | .ok program =>
    match functions : program.functions, signatures : program.signatures.functions with
    | [failedFunction, identityFunction], [failedSignature, identitySignature] =>
      let failedShape ← observeFailed failedFunction failedSignature
      let identityShape ← observeIdentity identityFunction identitySignature
      let ⟨methods⟩ ← observed (program.methods = []) "unexpected methods"
      let ⟨failedDeclaration⟩ ← observed (failedFunction.declaration = failedSignature.id) "failed declaration"
      let ⟨identityDeclaration⟩ ← observed (identityFunction.declaration = identitySignature.id) "identity declaration"
      let ⟨distinct⟩ ← observed (failedSignature.id ≠ identitySignature.id) "distinct declarations"
      let deep : CheckedProgramBodiesHaveStatementTyping program 1000 := {
        functions := by
          intro actual member candidate candidateMember accepted
          have identity := checkFunctionBody_success_declaration accepted
          simp only [functions, List.mem_cons, List.not_mem_nil, or_false] at member
          simp only [signatures, List.mem_cons, List.not_mem_nil, or_false] at candidateMember
          rcases member with rfl | rfl <;> rcases candidateMember with rfl | rfl
          · exact failedShape.statementTyping program.signatures
          · exact False.elim (distinct (failedDeclaration.symm.trans identity))
          · exact False.elim (distinct (identity.symm.trans identityDeclaration))
          · exact identityShape.statementTyping program.signatures
        methods := by intro method member; simp only [methods, List.not_mem_nil] at member }
      return ⟨program, checked, programWellFormed_ofCheckProgram_statements checked deep,
        failedFunction, identityFunction, failedSignature, identitySignature, functions, signatures, methods,
        failedDeclaration, identityDeclaration, distinct, failedShape, identityShape⟩
    | _, _ => throw (IO.userError "failure continuation declaration count")

end Tests.SourceCoreInitialLexicalFailure
