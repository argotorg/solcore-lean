import Solcore.SourceSemantics.SourceProgramCheckingSoundness
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
/-! Independent Source typing for a named function with scoped conditional returns. -/
namespace Tests.SourceCoreNamedBranch
open Solcore Frontend SourceInference SourceSemantics

structure Read (source : TypedSource) (binder : TypedBinder) (expected : TypeSystem.Ty) where
  node : ExpressionNode
  found : source.lookupExpression? node.id = some node
  form : node.form = .reference binder.name (.local binder.id)
  raw : node.rawType = expected
  type : node.type = expected
  requirements : node.requirements = []
  coercions : node.coercions = []

theorem Read.typed {source : TypedSource} {binder : TypedBinder} {expected : TypeSystem.Ty}
    (read : Read source binder expected) {context : SourceSemantics.Context}
    (scheme : binder.scheme = .mono expected) (requirements : binder.schemeRequirements = [])
    (word : TypeAdmissible context expected)
    (lookup : context.LocalLookup binder.id binder.scheme)
    (localRequirements : context.LocalSchemeRequirementsLookup binder.id binder.schemeRequirements) :
    ExpressionHasType source context read.node.id expected := by
  have instantiated : LocalSchemeInstantiationValid context binder expected [] := by
    refine .intro (LocalSchemeRequirementsWellFormed.empty _ _ requirements)
      (scheme.symm ▸ SchemeWellFormed.monoAdmissible word) [] ?_ ?_ ?_ (by simp) ?_ ?_
    · simpa only [scheme, TypeSystem.Scheme.mono] using ExactSubstitution.empty
    · intro metavariable replacement member; cases member
    · simpa only [scheme, TypeSystem.Scheme.mono] using SchemeInstantiates.empty_apply expected
    · intro id member; cases member
    · rw [instantiateLocalSchemePredicates, requirements]
      exact .nil
  have typed : ExpressionHasType source context read.node.id read.node.type := by
    refine .intro (lookupExpression?_sound read.found)
      (read.form ▸ ExpressionFormHasRawType.reference (.local lookup localRequirements instantiated))
      read.raw word (Eq.mp (congrArg (TypeAdmissible context) read.type.symm) word) ?_
    rw [read.requirements, read.coercions, read.type]
    exact .ordinary (by intro id member; cases member) (.nil _) rfl
  exact Eq.mp (congrArg (fun type => ExpressionHasType source context read.node.id type) read.type) typed

abbrev WordRead (source : TypedSource) (binder : TypedBinder) := Read source binder .word
abbrev BoolRead (source : TypedSource) (binder : TypedBinder) := Read source binder .bool

structure FactoryShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  flag : TypedBinder
  argument : TypedBinder
  copyBinder : TypedBinder
  conditionRead : BoolRead function.typedBody flag
  initialRead : WordRead function.typedBody argument
  localRead : WordRead function.typedBody copyBinder
  elseRead : WordRead function.typedBody argument
  initialized : StatementNode
  thenReturn : StatementNode
  elseReturn : StatementNode
  branch : StatementNode
  flagScheme : flag.scheme = .mono .bool
  flagRequirements : flag.schemeRequirements = []
  flagOrdinary : flag.comptime = false
  argumentScheme : argument.scheme = .mono .word
  argumentRequirements : argument.schemeRequirements = []
  argumentOrdinary : argument.comptime = false
  argumentFlag : argument.id ≠ flag.id
  localScheme : copyBinder.scheme = .mono .word
  localRequirements : copyBinder.schemeRequirements = []
  localOwner : copyBinder.id.owner = function.typedBody.owner
  localArgument : copyBinder.id ≠ argument.id
  localFlag : copyBinder.id ≠ flag.id
  localOrdinary : copyBinder.comptime = false
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.bool, .word]
  returns : signature.returnTypes = [.word]
  inputs : function.typedBody.inputs = [flag, argument]
  roots : function.typedBody.roots = [.statement branch.id]
  initializedFound : function.typedBody.lookupStatement? initialized.id = some initialized
  initializedForm : initialized.form = .letDecl copyBinder (some initialRead.node.id)
  initializedType : initialized.type = .unit
  thenReturnFound : function.typedBody.lookupStatement? thenReturn.id = some thenReturn
  thenReturnForm : thenReturn.form = .returnStmt (some localRead.node.id)
  thenReturnType : thenReturn.type = .word
  elseReturnFound : function.typedBody.lookupStatement? elseReturn.id = some elseReturn
  elseReturnForm : elseReturn.form = .returnStmt (some elseRead.node.id)
  elseReturnType : elseReturn.type = .word
  branchFound : function.typedBody.lookupStatement? branch.id = some branch
  branchForm : branch.form = .ifThen conditionRead.node.id [initialized.id, thenReturn.id] (some [elseReturn.id])
  branchType : branch.type = .word

def FactoryShape.body {function signature} (shape : FactoryShape function signature) : List StatementId :=
  [shape.branch.id]

def FactoryShape.nodeList {function signature} (shape : FactoryShape function signature) : List SourceInference.Node :=
  [.expression shape.conditionRead.node, .expression shape.initialRead.node,
    .statement shape.initialized, .expression shape.localRead.node, .statement shape.thenReturn,
    .expression shape.elseRead.node, .statement shape.elseReturn, .statement shape.branch]

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
  have same : statements = [shape.branch.id] := statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type := .word, hasValue := true, sawReturn := true, control := .returned}
  let ordinary : StatementFacts := {type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit}
  refine ⟨BodyFacts.singleton facts, rfl, ?_⟩
  intro lexical extension
  rw [shape.inputs, shape.inputTypes] at extension
  cases extension with
  | cons flagScheme flagExtended tail =>
    cases tail with
    | cons argumentScheme argumentExtended tail =>
      cases tail
      have binders : TypeParameterBindersWellFormed lexical := by
        rw [TypeParameterBindersWellFormed, argumentExtended.context_fields.2.2.1,
          flagExtended.context_fields.2.2.1]
        simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
          Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
      have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
      have bool : TypeAdmissible lexical .bool := ⟨binders, .builtin .bool⟩
      let locals := lexical.withLocal shape.copyBinder.id shape.copyBinder.scheme shape.copyBinder.schemeRequirements
      have localExtended : BinderExtends function.typedBody.owner lexical shape.copyBinder locals := by
        apply BinderExtends.intro
        · exact {
            owned := shape.localOwner
            scheme := shape.localScheme.symm ▸ SchemeWellFormed.monoAdmissible word
            quantified_fresh := by rw [shape.localScheme]; simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]
            monomorphic_requirements_empty := fun _ => shape.localRequirements }
        · cases argumentExtended
          cases flagExtended
          simp [LocalFresh, Context.withLocal, checkedBodyContext, declarationContext,
            Context.ofSignatures, Context.forDeclaration, Context.withAssumptions,
            Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.localArgument, shape.localFlag]
      have localWord : TypeAdmissible locals .word := ⟨binders, .builtin .word⟩
      have conditionTyped := shape.conditionRead.typed flagScheme shape.flagRequirements bool
        (by cases argumentExtended; exact .tail shape.argumentFlag flagExtended.local_self)
        (by cases argumentExtended; exact .tail shape.argumentFlag flagExtended.local_scheme_requirements_self)
      have initialTyped := shape.initialRead.typed argumentScheme shape.argumentRequirements word
        argumentExtended.local_self argumentExtended.local_scheme_requirements_self
      have elseTyped := shape.elseRead.typed argumentScheme shape.argumentRequirements word
        argumentExtended.local_self argumentExtended.local_scheme_requirements_self
      have localTyped := shape.localRead.typed shape.localScheme shape.localRequirements localWord
        localExtended.local_self localExtended.local_scheme_requirements_self
      have initializedTyped : StatementHasType function.typedBody ⟨.word, 0⟩ lexical shape.initialized.id locals ordinary := by
        apply StatementHasType.letInitialized (lookupStatement?_sound shape.initializedFound) shape.initializedForm
        · simpa only [shape.localScheme, TypeSystem.Scheme.mono] using initialTyped
        · rw [shape.localScheme]; rfl
        · rw [shape.localScheme]; rfl
        · exact localExtended
        · exact shape.initializedType
      have thenReturnTyped := StatementHasType.returnValue (control := ⟨.word, 0⟩)
        (lookupStatement?_sound shape.thenReturnFound) shape.thenReturnForm localTyped shape.thenReturnType
      have elseReturnTyped := StatementHasType.returnValue (control := ⟨.word, 0⟩)
        (lookupStatement?_sound shape.elseReturnFound) shape.elseReturnForm elseTyped shape.elseReturnType
      have branchTyped := StatementHasType.ifWithElse (lookupStatement?_sound shape.branchFound) shape.branchForm
        conditionTyped (.cons initializedTyped (.singleton thenReturnTyped)) (.singleton elseReturnTyped) shape.branchType
      exact ⟨lexical, .singleton branchTyped⟩

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function choose(flag: Bool, value: Word) returns (Word) { if (flag) { let copy: Word = value; return copy; } else { return value; } }"}] }

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

def observeRead (source : TypedSource) (binder : TypedBinder) (node : ExpressionNode) (expected : TypeSystem.Ty) : IO (Read source binder expected) := do
  let ⟨found⟩ ← observed (source.lookupExpression? node.id = some node) "read lookup"
  let ⟨form⟩ ← observed (node.form = .reference binder.name (.local binder.id)) "read binder"
  let ⟨raw⟩ ← observed (node.rawType = expected) "read raw Word"
  let ⟨type⟩ ← observed (node.type = expected) "read Word"
  let ⟨requirements⟩ ← observed (node.requirements = []) "read requirements"
  let ⟨coercions⟩ ← observed (node.coercions = []) "read coercions"
  return { node, found, form, raw, type, requirements, coercions }

def observeShape (function : CheckedFunction) (signature : ProgramFunctionSignature) : IO (FactoryShape function signature) := do
  let [flag, argument] := function.typedBody.inputs | throw (IO.userError "named branch inputs")
  let [.expression condition, .expression initial, .statement initialized,
      .expression copied, .statement thenReturn, .expression other, .statement elseReturn,
      .statement branch] := function.typedBody.nodes | throw (IO.userError "named branch graph")
  let .letDecl copyBinder _ := initialized.form | throw (IO.userError "copy binder")
  let conditionRead ← observeRead function.typedBody flag condition .bool
  let initialRead ← observeRead function.typedBody argument initial .word
  let localRead ← observeRead function.typedBody copyBinder copied .word
  let elseRead ← observeRead function.typedBody argument other .word
  let ⟨flagScheme⟩ ← observed (flag.scheme = .mono .bool) "named branch flagScheme"
  let ⟨flagRequirements⟩ ← observed (flag.schemeRequirements = []) "named branch flagRequirements"
  let ⟨flagOrdinary⟩ ← observed (flag.comptime = false) "named branch flagOrdinary"
  let ⟨argumentScheme⟩ ← observed (argument.scheme = .mono .word) "named branch argumentScheme"
  let ⟨argumentRequirements⟩ ← observed (argument.schemeRequirements = []) "named branch argumentRequirements"
  let ⟨argumentOrdinary⟩ ← observed (argument.comptime = false) "named branch argumentOrdinary"
  let ⟨argumentFlag⟩ ← observed (argument.id ≠ flag.id) "named branch argumentFlag"
  let ⟨localScheme⟩ ← observed (copyBinder.scheme = .mono .word) "named branch localScheme"
  let ⟨localRequirements⟩ ← observed (copyBinder.schemeRequirements = []) "named branch localRequirements"
  let ⟨localOwner⟩ ← observed (copyBinder.id.owner = function.typedBody.owner) "named branch localOwner"
  let ⟨localArgument⟩ ← observed (copyBinder.id ≠ argument.id) "named branch localArgument"
  let ⟨localFlag⟩ ← observed (copyBinder.id ≠ flag.id) "named branch localFlag"
  let ⟨localOrdinary⟩ ← observed (copyBinder.comptime = false) "named branch localOrdinary"
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "named branch parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.bool, .word]) "named branch inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.word]) "named branch returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [flag, argument]) "named branch inputs"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement branch.id]) "named branch roots"
  let ⟨initializedFound⟩ ← observed (function.typedBody.lookupStatement? initialized.id = some initialized) "named branch initializedFound"
  let ⟨initializedForm⟩ ← observed (initialized.form = .letDecl copyBinder (some initialRead.node.id)) "named branch initializedForm"
  let ⟨initializedType⟩ ← observed (initialized.type = .unit) "named branch initializedType"
  let ⟨thenReturnFound⟩ ← observed (function.typedBody.lookupStatement? thenReturn.id = some thenReturn) "named branch thenReturnFound"
  let ⟨thenReturnForm⟩ ← observed (thenReturn.form = .returnStmt (some localRead.node.id)) "named branch thenReturnForm"
  let ⟨thenReturnType⟩ ← observed (thenReturn.type = .word) "named branch thenReturnType"
  let ⟨elseReturnFound⟩ ← observed (function.typedBody.lookupStatement? elseReturn.id = some elseReturn) "named branch elseReturnFound"
  let ⟨elseReturnForm⟩ ← observed (elseReturn.form = .returnStmt (some elseRead.node.id)) "named branch elseReturnForm"
  let ⟨elseReturnType⟩ ← observed (elseReturn.type = .word) "named branch elseReturnType"
  let ⟨branchFound⟩ ← observed (function.typedBody.lookupStatement? branch.id = some branch) "named branch branchFound"
  let ⟨branchForm⟩ ← observed (branch.form = .ifThen conditionRead.node.id [initialized.id, thenReturn.id] (some [elseReturn.id])) "named branch branchForm"
  let ⟨branchType⟩ ← observed (branch.type = .word) "named branch branchType"
  return { flag, argument, copyBinder, conditionRead, initialRead, localRead, elseRead, initialized, thenReturn, elseReturn, branch, flagScheme, flagRequirements, flagOrdinary, argumentScheme, argumentRequirements, argumentOrdinary, argumentFlag, localScheme, localRequirements, localOwner, localArgument, localFlag, localOrdinary, parameters, inputTypes, returns, inputs, roots, initializedFound, initializedForm, initializedType, thenReturnFound, thenReturnForm, thenReturnType, elseReturnFound, elseReturnForm, elseReturnType, branchFound, branchForm, branchType }

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
        let ⟨nodes⟩ ← observed (function.typedBody.nodes = sourceShape.nodeList) "complete named branch graph"
        return ⟨program, checked, programWellFormed_ofCheckProgram_statements checked deep,
          function, signature, functions, signatures, methods, sourceShape, nodes⟩
      else throw (IO.userError "unexpected named branch methods")
    | _, _ => throw (IO.userError "named branch declaration count")

end Tests.SourceCoreNamedBranch
