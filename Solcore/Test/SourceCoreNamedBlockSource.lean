import Solcore.Test.SourceCoreNamedBranchSource
/-! Independent Source typing for a block-local allocation followed by mutation
of an outer parameter. The return reads that parameter after the block ends. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreNamedBlock
open Solcore Frontend SourceInference SourceSemantics
abbrev Read := Tests.SourceCoreNamedBranch.Read

structure FactoryShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  value : TypedBinder
  argument : TypedBinder
  copyBinder : TypedBinder
  initialRead : Read function.typedBody argument .word
  localRead : Read function.typedBody copyBinder .word
  finalRead : Read function.typedBody value .word
  initialized : StatementNode
  assignment : StatementNode
  resolution : AssignmentResolution
  blockNode : StatementNode
  statement : StatementNode
  valueScheme : value.scheme = .mono .word
  valueRequirements : value.schemeRequirements = []
  valueOrdinary : value.comptime = false
  valueOwner : value.id.owner = function.typedBody.owner
  argumentScheme : argument.scheme = .mono .word
  argumentRequirements : argument.schemeRequirements = []
  argumentOrdinary : argument.comptime = false
  argumentValue : argument.id ≠ value.id
  localScheme : copyBinder.scheme = .mono .word
  localRequirements : copyBinder.schemeRequirements = []
  localOrdinary : copyBinder.comptime = false
  localOwner : copyBinder.id.owner = function.typedBody.owner
  localValue : copyBinder.id ≠ value.id
  localArgument : copyBinder.id ≠ argument.id
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word, .word]
  returns : signature.returnTypes = [.word]
  inputs : function.typedBody.inputs = [value, argument]
  roots : function.typedBody.roots = [.statement blockNode.id, .statement statement.id]
  initializedFound : function.typedBody.lookupStatement? initialized.id = some initialized
  initializedForm : initialized.form = .letDecl copyBinder (some initialRead.node.id)
  initializedType : initialized.type = .unit
  assignmentFound : function.typedBody.lookupStatement? assignment.id = some assignment
  assignmentForm : assignment.form = .assignValue resolution .equal localRead.node.id
  assignmentType : assignment.type = .unit
  targetRoot : resolution.target.root = value.id
  targetType : resolution.target.type = .word
  targetBare : resolution.target.projections = []
  assignmentRequirements : resolution.requirements = []
  blockFound : function.typedBody.lookupStatement? blockNode.id = some blockNode
  blockForm : blockNode.form = .block [initialized.id, assignment.id]
  blockType : blockNode.type = .unit
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some finalRead.node.id)
  statementType : statement.type = .word

def FactoryShape.body {function signature} (shape : FactoryShape function signature) : List StatementId :=
  [shape.blockNode.id, shape.statement.id]

def FactoryShape.nodeList {function signature} (shape : FactoryShape function signature) : List SourceInference.Node :=
  [.expression shape.initialRead.node, .statement shape.initialized,
    .expression shape.localRead.node, .statement shape.assignment, .statement shape.blockNode,
    .expression shape.finalRead.node, .statement shape.statement]

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
  have same : statements = [shape.blockNode.id, shape.statement.id] := statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type := .word, hasValue := true, sawReturn := true, control := .returned}
  let ordinary : StatementFacts := {type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit}
  refine ⟨BodyFacts.cons ordinary (BodyFacts.singleton facts), rfl, ?_⟩
  intro lexical extension
  rw [shape.inputs, shape.inputTypes] at extension
  cases extension with
  | cons valueScheme valueExtended tail =>
    cases tail with
    | cons argumentScheme argumentExtended tail =>
      cases tail
      have binders : TypeParameterBindersWellFormed lexical := by
        rw [TypeParameterBindersWellFormed, argumentExtended.context_fields.2.2.1,
          valueExtended.context_fields.2.2.1]
        simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
          Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
      have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
      let locals := lexical.withLocal shape.copyBinder.id shape.copyBinder.scheme shape.copyBinder.schemeRequirements
      have localExtended : BinderExtends function.typedBody.owner lexical shape.copyBinder locals := by
        apply BinderExtends.intro
        · exact {
            owned := shape.localOwner
            scheme := shape.localScheme.symm ▸ SchemeWellFormed.monoAdmissible word
            quantified_fresh := by rw [shape.localScheme]; simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]
            monomorphic_requirements_empty := fun _ => shape.localRequirements }
        · cases argumentExtended
          cases valueExtended
          simp [LocalFresh, Context.withLocal, checkedBodyContext, declarationContext,
            Context.ofSignatures, Context.forDeclaration, Context.withAssumptions,
            Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.localArgument, shape.localValue]
      have localWord : TypeAdmissible locals .word := ⟨binders, .builtin .word⟩
      have initialTyped := shape.initialRead.typed argumentScheme shape.argumentRequirements word
        argumentExtended.local_self argumentExtended.local_scheme_requirements_self
      have localTyped := shape.localRead.typed shape.localScheme shape.localRequirements localWord
        localExtended.local_self localExtended.local_scheme_requirements_self
      have valueLookup : lexical.LocalLookup shape.value.id shape.value.scheme := by
        cases argumentExtended
        exact .tail shape.argumentValue valueExtended.local_self
      have finalTyped := shape.finalRead.typed valueScheme shape.valueRequirements word valueLookup
        (by cases argumentExtended; exact .tail shape.argumentValue valueExtended.local_scheme_requirements_self)
      have initializedTyped : StatementHasType function.typedBody ⟨.word, 0⟩ lexical shape.initialized.id locals ordinary := by
        apply StatementHasType.letInitialized (lookupStatement?_sound shape.initializedFound) shape.initializedForm
        · simpa only [shape.localScheme, TypeSystem.Scheme.mono] using initialTyped
        · rw [shape.localScheme]; rfl
        · rw [shape.localScheme]; rfl
        · exact localExtended
        · exact shape.initializedType
      have writable : WritableLocal locals shape.resolution.target.root .word := by
        rw [shape.targetRoot]
        exact .intro (.tail shape.localValue valueLookup)
          (valueScheme.symm ▸ SchemeWellFormed.monoAdmissible localWord)
          (by rw [valueScheme]; rfl) (by rw [valueScheme]; rfl)
      have assignmentTyped : SourceAssignmentHasType function.typedBody locals shape.resolution .equal shape.localRead.node.id :=
        .equal (.intro writable (by rw [shape.targetBare]; exact .nil _) shape.targetType) localTyped shape.assignmentRequirements
      have assigned : StatementHasType function.typedBody ⟨.word, 0⟩ locals shape.assignment.id locals ordinary :=
        .assignValue (lookupStatement?_sound shape.assignmentFound) shape.assignmentForm assignmentTyped shape.assignmentType
      have blockTyped : StatementHasType function.typedBody ⟨.word, 0⟩ lexical shape.blockNode.id lexical ordinary :=
        .block (lookupStatement?_sound shape.blockFound) shape.blockForm
          (.cons initializedTyped (.singleton assigned)) shape.blockType
      have returned := StatementHasType.returnValue (control := ⟨.word, 0⟩)
        (lookupStatement?_sound shape.statementFound) shape.statementForm finalTyped shape.statementType
      exact ⟨lexical, .cons blockTyped (.singleton returned)⟩

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function update(value: Word, next: Word) returns (Word) { { let copy: Word = next; value = copy; } return value; }"}] }

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

def observeRead (source : TypedSource) (binder : TypedBinder) (node : ExpressionNode) : IO (Read source binder .word) := do
  let ⟨found⟩ ← observed (source.lookupExpression? node.id = some node) "read lookup"
  let ⟨form⟩ ← observed (node.form = .reference binder.name (.local binder.id)) "read binder"
  let ⟨raw⟩ ← observed (node.rawType = .word) "read raw Word"
  let ⟨type⟩ ← observed (node.type = .word) "read Word"
  let ⟨requirements⟩ ← observed (node.requirements = []) "read requirements"
  let ⟨coercions⟩ ← observed (node.coercions = []) "read coercions"
  return { node, found, form, raw, type, requirements, coercions }

def observeShape (function : CheckedFunction) (signature : ProgramFunctionSignature) : IO (FactoryShape function signature) := do
  let [value, argument] := function.typedBody.inputs | throw (IO.userError "named block inputs")
  let [.expression initial, .statement initialized, .expression copyRead, .statement assignment,
      .statement blockNode, .expression result, .statement statement] := function.typedBody.nodes
    | throw (IO.userError "named block graph")
  let .letDecl copyBinder _ := initialized.form | throw (IO.userError "block local allocation")
  let .assignValue resolution .equal _ := assignment.form | throw (IO.userError "bare value assignment")
  let initialRead ← observeRead function.typedBody argument initial
  let localRead ← observeRead function.typedBody copyBinder copyRead
  let finalRead ← observeRead function.typedBody value result
  let ⟨valueScheme⟩ ← observed (value.scheme = .mono .word) "named block valueScheme"
  let ⟨valueRequirements⟩ ← observed (value.schemeRequirements = []) "named block valueRequirements"
  let ⟨valueOrdinary⟩ ← observed (value.comptime = false) "named block valueOrdinary"
  let ⟨valueOwner⟩ ← observed (value.id.owner = function.typedBody.owner) "named block valueOwner"
  let ⟨argumentScheme⟩ ← observed (argument.scheme = .mono .word) "named block argumentScheme"
  let ⟨argumentRequirements⟩ ← observed (argument.schemeRequirements = []) "named block argumentRequirements"
  let ⟨argumentOrdinary⟩ ← observed (argument.comptime = false) "named block argumentOrdinary"
  let ⟨argumentValue⟩ ← observed (argument.id ≠ value.id) "named block argumentValue"
  let ⟨localScheme⟩ ← observed (copyBinder.scheme = .mono .word) "named block localScheme"
  let ⟨localRequirements⟩ ← observed (copyBinder.schemeRequirements = []) "named block localRequirements"
  let ⟨localOrdinary⟩ ← observed (copyBinder.comptime = false) "named block localOrdinary"
  let ⟨localOwner⟩ ← observed (copyBinder.id.owner = function.typedBody.owner) "named block localOwner"
  let ⟨localValue⟩ ← observed (copyBinder.id ≠ value.id) "named block localValue"
  let ⟨localArgument⟩ ← observed (copyBinder.id ≠ argument.id) "named block localArgument"
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "named block parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word, .word]) "named block inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.word]) "named block returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [value, argument]) "named block inputs"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement blockNode.id, .statement statement.id]) "named block roots"
  let ⟨initializedFound⟩ ← observed (function.typedBody.lookupStatement? initialized.id = some initialized) "named block initializedFound"
  let ⟨initializedForm⟩ ← observed (initialized.form = .letDecl copyBinder (some initialRead.node.id)) "named block initializedForm"
  let ⟨initializedType⟩ ← observed (initialized.type = .unit) "named block initializedType"
  let ⟨assignmentFound⟩ ← observed (function.typedBody.lookupStatement? assignment.id = some assignment) "named block assignmentFound"
  let ⟨assignmentForm⟩ ← observed (assignment.form = .assignValue resolution .equal localRead.node.id) "named block assignmentForm"
  let ⟨assignmentType⟩ ← observed (assignment.type = .unit) "named block assignmentType"
  let ⟨targetRoot⟩ ← observed (resolution.target.root = value.id) "named block targetRoot"
  let ⟨targetType⟩ ← observed (resolution.target.type = .word) "named block targetType"
  let ⟨targetBare⟩ ← observed (resolution.target.projections = []) "named block targetBare"
  let ⟨assignmentRequirements⟩ ← observed (resolution.requirements = []) "named block assignmentRequirements"
  let ⟨blockFound⟩ ← observed (function.typedBody.lookupStatement? blockNode.id = some blockNode) "named block blockFound"
  let ⟨blockForm⟩ ← observed (blockNode.form = .block [initialized.id, assignment.id]) "named block blockForm"
  let ⟨blockType⟩ ← observed (blockNode.type = .unit) "named block blockType"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "named block statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some finalRead.node.id)) "named block statementForm"
  let ⟨statementType⟩ ← observed (statement.type = .word) "named block statementType"
  return { value, argument, copyBinder, initialRead, localRead, finalRead, initialized, assignment, resolution, blockNode, statement, valueScheme, valueRequirements, valueOrdinary, valueOwner, argumentScheme, argumentRequirements, argumentOrdinary, argumentValue, localScheme, localRequirements, localOrdinary, localOwner, localValue, localArgument, parameters, inputTypes, returns, inputs, roots, initializedFound, initializedForm, initializedType, assignmentFound, assignmentForm, assignmentType, targetRoot, targetType, targetBare, assignmentRequirements, blockFound, blockForm, blockType, statementFound, statementForm, statementType }

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
  nodes : function.typedBody.nodes = sourceShape.nodeList

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
        let ⟨nodes⟩ ← observed (function.typedBody.nodes = sourceShape.nodeList) "complete named block graph"
        return ⟨program, checked, programWellFormed_ofCheckProgram_statements checked deep,
          function, signature, functions, signatures, methods, sourceShape, nodes⟩
      else throw (IO.userError "unexpected named block methods")
    | _, _ => throw (IO.userError "named block declaration count")

end Tests.SourceCoreNamedBlock
