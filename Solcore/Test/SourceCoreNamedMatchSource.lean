import Solcore.Test.SourceCoreNamedBranchSource
/-! Independent Source typing for a match-pattern allocation followed by mutation
of an outer parameter. The return reads that parameter after the selected arm ends. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreNamedMatch
open Solcore Frontend SourceInference SourceSemantics
abbrev Read := Tests.SourceCoreNamedBranch.Read

structure FactoryShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  value : TypedBinder
  argument : TypedBinder
  copyBinder : TypedBinder
  initialRead : Read function.typedBody argument .word
  localRead : Read function.typedBody copyBinder .word
  finalRead : Read function.typedBody value .word
  assignment : StatementNode
  resolution : AssignmentResolution
  matchNode : StatementNode
  matching : MatchResolution
  arm : TypedMatchCase
  patternSpan : Syntax.SourceSpan
  owner : function.typedBody.owner = signature.id
  hiddenValue : matching.hiddenScrutinee ≠ value.id
  hiddenArgument : matching.hiddenScrutinee ≠ argument.id
  localHidden : copyBinder.id ≠ matching.hiddenScrutinee
  scrutinee : matching.scrutinee = initialRead.node.id
  arms : matching.cases = [arm]
  noDefault : matching.defaultBody = none
  matchRequirements : matching.requirements = []
  armBody : arm.body = [assignment.id]
  patternSource : arm.pattern.source = .binder patternSpan copyBinder.name
  patternResolution : arm.pattern.resolution = .binder copyBinder
  patternType : arm.pattern.type = .word
  patternRequirements : arm.pattern.requirements = []
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
  roots : function.typedBody.roots = [.statement matchNode.id, .statement statement.id]
  assignmentFound : function.typedBody.lookupStatement? assignment.id = some assignment
  assignmentForm : assignment.form = .assignValue resolution .equal localRead.node.id
  assignmentType : assignment.type = .unit
  targetRoot : resolution.target.root = value.id
  targetType : resolution.target.type = .word
  targetBare : resolution.target.projections = []
  assignmentRequirements : resolution.requirements = []
  matchFound : function.typedBody.lookupStatement? matchNode.id = some matchNode
  matchForm : matchNode.form = .matchWith matching
  matchType : matchNode.type = .unit
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some finalRead.node.id)
  statementType : statement.type = .word

def FactoryShape.body {function signature} (shape : FactoryShape function signature) : List StatementId :=
  [shape.matchNode.id, shape.statement.id]

def FactoryShape.nodeList {function signature} (shape : FactoryShape function signature) : List SourceInference.Node :=
  [.expression shape.initialRead.node, .expression shape.localRead.node, .statement shape.assignment, .statement shape.matchNode,
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
  have same : statements = [shape.matchNode.id, shape.statement.id] := statementRoots_injective (roots.symm.trans shape.roots)
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
      have writable : WritableLocal locals shape.resolution.target.root .word := by
        rw [shape.targetRoot]
        exact .intro (.tail shape.localValue valueLookup)
          (valueScheme.symm ▸ SchemeWellFormed.monoAdmissible localWord)
          (by rw [valueScheme]; rfl) (by rw [valueScheme]; rfl)
      have assignmentTyped : SourceAssignmentHasType function.typedBody locals shape.resolution .equal shape.localRead.node.id :=
        .equal (.intro writable (by rw [shape.targetBare]; exact .nil _) shape.targetType) localTyped shape.assignmentRequirements
      have assigned : StatementHasType function.typedBody ⟨.word, 0⟩ locals shape.assignment.id locals ordinary :=
        .assignValue (lookupStatement?_sound shape.assignmentFound) shape.assignmentForm assignmentTyped shape.assignmentType
      have patternSource : MatchPatternSourceRepresents lexical shape.arm.pattern.source
          shape.arm.pattern.resolution 0 := by
        rw [shape.patternSource, shape.patternResolution]
        exact .binder rfl
      have patternBinder : PatternBinderValid lexical .word shape.copyBinder := {
        scheme_eq := shape.localScheme
        runtime := shape.localOrdinary
        wellFormed := by
          intro declaration current
          have same : declaration = function.typedBody.owner := by
            rw [argumentExtended.context_fields.2.1, valueExtended.context_fields.2.1] at current
            have owner : signature.id = declaration := Option.some.inj current
            exact owner.symm.trans shape.owner.symm
          rw [same]
          cases localExtended with
          | intro wellFormed _ => exact wellFormed }
      have patternTyped : TypedMatchPatternHasType lexical shape.arm.pattern .word [shape.copyBinder] 0 := {
        type_eq := shape.patternType
        source_represents := patternSource
        resolution_type := by
          rw [shape.patternResolution, shape.patternRequirements]
          exact .binder patternBinder
        binders_distinct := ⟨by simp, by simp⟩ }
      have armTyped : MatchCaseHasType function.typedBody ⟨.word, 0⟩ lexical .word
          shape.arm (BodyFacts.singleton ordinary) :=
        .intro patternTyped (.cons localExtended (.nil _))
          (shape.armBody.symm ▸ StatementsHaveType.singleton assigned)
      have matched : StatementHasType function.typedBody ⟨.word, 0⟩ lexical shape.matchNode.id lexical ordinary := by
        apply StatementHasType.matchWithoutDefault
          (caseFacts := [BodyFacts.singleton ordinary]) (summary := .ordinary .unit)
          (lookupStatement?_sound shape.matchFound) shape.matchForm shape.noDefault
        · rw [shape.scrutinee]; exact initialTyped
        · rw [shape.arms]; exact .cons armTyped (.nil _ _ _)
        · rw [shape.matchRequirements, shape.arms]; simp [shape.patternRequirements]
        · rw [shape.arms]
          apply MatchExhaustive.catchall (matchCase := shape.arm) (.head _)
          refine ⟨0, patternSource, ?_⟩
          rw [shape.patternResolution]
          exact .binder
        · rfl
        · exact shape.matchType
      have returned := StatementHasType.returnValue (control := ⟨.word, 0⟩)
        (lookupStatement?_sound shape.statementFound) shape.statementForm finalTyped shape.statementType
      exact ⟨lexical, .cons matched (.singleton returned)⟩

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function update(value: Word, next: Word) returns (Word) { match (next) { case copy { value = copy; } } return value; }"}] }

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
  let [value, argument] := function.typedBody.inputs | throw (IO.userError "named match inputs")
  let [.expression initial, .expression copyRead, .statement assignment,
      .statement matchNode, .expression result, .statement statement] := function.typedBody.nodes
    | throw (IO.userError "named match graph")
  let .matchWith matching := matchNode.form | throw (IO.userError "match statement")
  let [arm] := matching.cases | throw (IO.userError "single pattern arm")
  let .binder copyBinder := arm.pattern.resolution | throw (IO.userError "binder pattern")
  let .binder patternSpan _ := arm.pattern.source | throw (IO.userError "original binder pattern")
  let .assignValue resolution .equal _ := assignment.form | throw (IO.userError "bare value assignment")
  let initialRead ← observeRead function.typedBody argument initial
  let localRead ← observeRead function.typedBody copyBinder copyRead
  let finalRead ← observeRead function.typedBody value result
  let ⟨valueScheme⟩ ← observed (value.scheme = .mono .word) "named match valueScheme"
  let ⟨valueRequirements⟩ ← observed (value.schemeRequirements = []) "named match valueRequirements"
  let ⟨valueOrdinary⟩ ← observed (value.comptime = false) "named match valueOrdinary"
  let ⟨valueOwner⟩ ← observed (value.id.owner = function.typedBody.owner) "named match valueOwner"
  let ⟨argumentScheme⟩ ← observed (argument.scheme = .mono .word) "named match argumentScheme"
  let ⟨argumentRequirements⟩ ← observed (argument.schemeRequirements = []) "named match argumentRequirements"
  let ⟨argumentOrdinary⟩ ← observed (argument.comptime = false) "named match argumentOrdinary"
  let ⟨argumentValue⟩ ← observed (argument.id ≠ value.id) "named match argumentValue"
  let ⟨localScheme⟩ ← observed (copyBinder.scheme = .mono .word) "named match localScheme"
  let ⟨localRequirements⟩ ← observed (copyBinder.schemeRequirements = []) "named match localRequirements"
  let ⟨localOrdinary⟩ ← observed (copyBinder.comptime = false) "named match localOrdinary"
  let ⟨localOwner⟩ ← observed (copyBinder.id.owner = function.typedBody.owner) "named match localOwner"
  let ⟨localValue⟩ ← observed (copyBinder.id ≠ value.id) "named match localValue"
  let ⟨localArgument⟩ ← observed (copyBinder.id ≠ argument.id) "named match localArgument"
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "named match parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word, .word]) "named match inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.word]) "named match returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [value, argument]) "named match inputs"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement matchNode.id, .statement statement.id]) "named match roots"
  let ⟨assignmentFound⟩ ← observed (function.typedBody.lookupStatement? assignment.id = some assignment) "named match assignmentFound"
  let ⟨assignmentForm⟩ ← observed (assignment.form = .assignValue resolution .equal localRead.node.id) "named match assignmentForm"
  let ⟨assignmentType⟩ ← observed (assignment.type = .unit) "named match assignmentType"
  let ⟨targetRoot⟩ ← observed (resolution.target.root = value.id) "named match targetRoot"
  let ⟨targetType⟩ ← observed (resolution.target.type = .word) "named match targetType"
  let ⟨targetBare⟩ ← observed (resolution.target.projections = []) "named match targetBare"
  let ⟨assignmentRequirements⟩ ← observed (resolution.requirements = []) "named match assignmentRequirements"
  let ⟨matchFound⟩ ← observed (function.typedBody.lookupStatement? matchNode.id = some matchNode) "named match matchFound"
  let ⟨matchForm⟩ ← observed (matchNode.form = .matchWith matching) "named match matchForm"
  let ⟨matchType⟩ ← observed (matchNode.type = .unit) "named match matchType"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "named match statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some finalRead.node.id)) "named match statementForm"
  let ⟨statementType⟩ ← observed (statement.type = .word) "named match statementType"
  let ⟨owner⟩ ← observed (function.typedBody.owner = signature.id) "named match owner"
  let ⟨hiddenValue⟩ ← observed (matching.hiddenScrutinee ≠ value.id) "named match hiddenValue"
  let ⟨hiddenArgument⟩ ← observed (matching.hiddenScrutinee ≠ argument.id) "named match hiddenArgument"
  let ⟨localHidden⟩ ← observed (copyBinder.id ≠ matching.hiddenScrutinee) "named match localHidden"
  let ⟨scrutinee⟩ ← observed (matching.scrutinee = initialRead.node.id) "named match scrutinee"
  let ⟨arms⟩ ← observed (matching.cases = [arm]) "named match arms"
  let ⟨noDefault⟩ ← observed (matching.defaultBody = none) "named match noDefault"
  let ⟨matchRequirements⟩ ← observed (matching.requirements = []) "named match matchRequirements"
  let ⟨armBody⟩ ← observed (arm.body = [assignment.id]) "named match armBody"
  let ⟨patternSource⟩ ← observed (arm.pattern.source = .binder patternSpan copyBinder.name) "named match patternSource"
  let ⟨patternResolution⟩ ← observed (arm.pattern.resolution = .binder copyBinder) "named match patternResolution"
  let ⟨patternType⟩ ← observed (arm.pattern.type = .word) "named match patternType"
  let ⟨patternRequirements⟩ ← observed (arm.pattern.requirements = []) "named match patternRequirements"
  return { value, argument, copyBinder, initialRead, localRead, finalRead, assignment, resolution, matchNode, matching, arm, patternSpan, owner, hiddenValue, hiddenArgument, localHidden, scrutinee, arms, noDefault, matchRequirements, armBody, patternSource, patternResolution, patternType, patternRequirements, statement, valueScheme, valueRequirements, valueOrdinary, valueOwner, argumentScheme, argumentRequirements, argumentOrdinary, argumentValue, localScheme, localRequirements, localOrdinary, localOwner, localValue, localArgument, parameters, inputTypes, returns, inputs, roots, assignmentFound, assignmentForm, assignmentType, targetRoot, targetType, targetBare, assignmentRequirements, matchFound, matchForm, matchType, statementFound, statementForm, statementType }

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
        let ⟨nodes⟩ ← observed (function.typedBody.nodes = sourceShape.nodeList) "complete named match graph"
        return ⟨program, checked, programWellFormed_ofCheckProgram_statements checked deep,
          function, signature, functions, signatures, methods, sourceShape, nodes⟩
      else throw (IO.userError "unexpected named match methods")
    | _, _ => throw (IO.userError "named match declaration count")

end Tests.SourceCoreNamedMatch
