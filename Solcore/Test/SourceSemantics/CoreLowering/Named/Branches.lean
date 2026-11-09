import Solcore.SourceSemantics.SourceProgramCheckingSoundness
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.PhysicalPublic
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.LambdaBodySupport
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicInputRegistries
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.SelectedBodyCompiler
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalNamedCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.Bootstrap
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.CallRejection
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.InitializedPublicBounds
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.LambdaBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.OrdinarySequenceCallers
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.BranchingTrees
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericImperativeMatchMeaning
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedEvidenceRoots
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NamedCollectors
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicActualRegistry
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicDirectHistories
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PatternsAndArms

/-!
# Named branch tests

Named functions with blocks, branches and matches.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreNamedBranchSource
/-! Independent Source typing for a named function with scoped conditional returns. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

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
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedBlockSource
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedBlockFixture
/-! Actual compilation, selected inventory and static block observations for
one named Word function with an inner allocation, outer mutation and return. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreNamedBlock
open Solcore Frontend SourceInference SourceSemantics

private def observeFact (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

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
  let signature :: _ := checked.program.signatures.functions
    | throw (IO.userError "factory signature missing")
  let seeds := [SourceCompiler.Seed.declaration signature.id]
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

structure ObservedFactory (fixture : CompiledFixture) where
  row : SourceSpecialization.SpecializedFunction
  shape : FactoryShape row.function fixture.signature
  member : row ∈ fixture.recipe.compiled.validationPlan.specializations
  sourceOwner : row.function.typedBody.owner = fixture.signature.id
  parameters : row.parameterSubstitution = []
  closed : row.assumptions = []
  ordinary : row.function.returnComptime = false
  resultType : row.function.inferredBodyType = .word
  target : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
    (CallableNamedMetadata.instantiation row) = .ok row.key
  nodes : row.function.typedBody.nodes = shape.nodeList
  noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []
  profile : fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true
  entry : SourceCoreCallableIndexedPrograms.Entry fixture.recipe.compiled.indexed.layouts
  entryMember : entry ∈ fixture.recipe.compiled.indexed.entries

abbrev ObservedFactory.inputs {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.inputs
abbrev ObservedFactory.roots {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.roots
abbrev ObservedFactory.value {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.value
abbrev ObservedFactory.argument {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.argument
abbrev ObservedFactory.binderScheme {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.argumentScheme

private def observeTarget (fixture : CompiledFixture) (row : SourceSpecialization.SpecializedFunction) :
    IO (PLift (SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) = .ok row.key)) := do
  match accepted : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) with
  | .error error => throw (IO.userError (reprStr error))
  | .ok key =>
    let ⟨same⟩ ← observeFact (key = row.key) "captured factory exact key"
    return ⟨by rw [accepted, same]⟩

def observeFactory (fixture : CompiledFixture) : IO (ObservedFactory fixture) := do
  match rows : fixture.recipe.compiled.validationPlan.specializations with
  | [row] =>
    let shape ← observeShape row.function fixture.signature
    match entries : fixture.recipe.compiled.indexed.entries with
    | [entry] =>
      let ⟨sourceOwner⟩ ← observeFact (row.function.typedBody.owner = fixture.signature.id) "named block source owner"
      let ⟨parameters⟩ ← observeFact (row.parameterSubstitution = []) "named block substitution"
      let ⟨closed⟩ ← observeFact (row.assumptions = []) "named block assumptions"
      let ⟨resultType⟩ ← observeFact (row.function.inferredBodyType = .word) "named block result type"
      let ⟨ordinary⟩ ← observeFact (row.function.returnComptime = false) "named block ordinary result"
      let ⟨target⟩ ← observeTarget fixture row
      let ⟨nodes⟩ ← observeFact (row.function.typedBody.nodes = shape.nodeList) "named block nodes"
      let ⟨noLocals⟩ ← observeFact (fixture.recipe.compiled.indexed.base.locals.bindings = []) "named block local catalog"
      let ⟨profile⟩ ← observeFact (fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true) "named block profile"
      return {
        row, shape, sourceOwner, parameters, closed, ordinary, resultType, target, nodes, noLocals, profile, entry
        member := by rw [rows]; exact .head []
        entryMember := by rw [entries]; exact .head [] }
    | _ => throw (IO.userError "named block entry count")
  | _ => throw (IO.userError "named block specialization count")

/-- The staged selection is obtained from the retained callable table and
original sidecar of the concrete compiler result. -/
structure ObservedStages (fixture : CompiledFixture)
    (observed : ObservedFactory fixture) where
  singletonGlobal : fixture.recipe.compiled.indexed.base.globals.length = 1
  descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named observed.row.key)
  native : SourceCoreGeneralFunctions.CallableContext
  present : fixture.recipe.compiled.indexed.base.callableContext = some native
  sidecar : SourceCoreStageContracts.Sidecar
  issued : SourceCoreStageContracts.prepareSidecar
    fixture.recipe.compiled.indexed.base.plan observed.row.key = .ok sidecar

def observeStages (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ObservedStages fixture observed) := do
  match present : fixture.recipe.compiled.indexed.base.callableContext with
  | none => throw (IO.userError "factory callable context missing")
  | some native =>
    match issued : SourceCoreStageContracts.prepareSidecar
        fixture.recipe.compiled.indexed.base.plan observed.row.key with
    | .error _ => throw (IO.userError "factory original sidecar missing")
    | .ok sidecar =>
      if singletonGlobal : fixture.recipe.compiled.indexed.base.globals.length = 1 then
        match SourceCoreCallableContracts.descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
            (.named observed.row.key) with
        | .error error => throw (IO.userError (reprStr error))
        | .ok descriptor => return ⟨singletonGlobal, descriptor, native, present, sidecar, issued⟩
      else throw (IO.userError "factory global count")

def ObservedStages.registry {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (_actual : ObservedStages fixture observed) : Staging.Recursive.Registry :=
  RecursiveNamedPreparedStageScopes.registry
    (RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected)

theorem ObservedStages.selected {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    stages.registry.Closure actual.header.function
      (RecursiveStageRegistry.scope stages.sidecar [] actual.header.function) := by
  have same := RecursiveNamedPreparedStageScopes.sidecar_caller stages.issued
    (CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.record actual.prepared actual.aligned)
  rw [actual.aligned.function]
  exact RecursiveNamedPreparedStageScopes.Selected.named actual.prepared stages.sidecar stages.issued same


theorem ActualHeader.complete {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [actual.header] := by
  have selected := CallableIndexedPreparedInventories.cached_global_at fixture.recipe.compiled actual.prepared.selected
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  rw [stages.singletonGlobal] at bound
  have zero : actual.prepared.index = 0 := by omega
  intro index signature found
  have bound := (List.getElem?_eq_some_iff.mp found).1
  rw [stages.singletonGlobal] at bound
  have indexZero : index = 0 := by omega
  refine ⟨actual.header, .head [], actual.aligned.slot.trans (zero.trans indexZero.symm), ?_⟩
  rw [actual.aligned.named]
  rw [zero] at selected
  rw [indexZero] at found
  exact Option.some.inj (selected.symm.trans found)

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


theorem ObservedStages.inventory {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) :
    ∃ input : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled,
      input.row = observed.row ∧
      ∃ packet : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued input,
      ∃ actual : ActualHeader fixture observed.row, actual.header = packet.header := by
  obtain ⟨prepared⟩ := fixture.prepared observed.member
  have range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures fixture.recipe.compiled.sourceProgram.signatures) observed.row.parameterSubstitution := by
    simp only [observed.parameters, SourceSemantics.ParameterSubstitution.RangeWellFormed,
      List.not_mem_nil, false_implies, implies_true]
  have metadata : CallableNamedCanonicalOrder.retainedInstantiation observed.row =
      CallableNamedMetadata.instantiation observed.row := by
    simp [CallableNamedCanonicalOrder.retainedInstantiation, CallableNamedMetadata.instantiation, observed.parameters]
  have target : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedCanonicalOrder.retainedInstantiation observed.row) = .ok prepared.named.signature.key := by
    rw [metadata, RecursiveNamedPreparedCallEvidence.Prepared.signature_key prepared]
    exact observed.target
  have selected := CallableIndexedPreparedInventories.cached_global_at fixture.recipe.compiled prepared.selected
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  rw [stages.singletonGlobal] at bound
  have zero : prepared.index = 0 := by omega
  have globals : fixture.recipe.compiled.indexed.base.globals = [prepared.named.signature] := by
    obtain ⟨first, single⟩ := List.length_eq_one_iff.mp stages.singletonGlobal
    rw [single, zero] at selected
    have same : first = prepared.named.signature := by simpa only [List.getElem?_cons_zero, Option.some.injEq] using selected
    exact single.trans (congrArg (fun value => [value]) same)
  let input : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled := {
    row := observed.row
    prepared := prepared
    range := range
    ordinaryReturn := observed.ordinary
    ordinaryParameters := by
      intro binder member
      rw [observed.inputs] at member
      rcases List.mem_cons.mp member with same | rest
      · exact same ▸ observed.shape.valueOrdinary
      · have same := List.mem_singleton.mp rest
        exact same ▸ observed.shape.argumentOrdinary
    target := target
    slot := by simp only [CallableNamedMetadata.Slot, globals, zero]; simp }
  obtain ⟨packet⟩ := CallableIndexedOwnedPreparedFiniteNamedInventories.issue fixture.source_wellFormed input
  let actual : ActualHeader fixture observed.row := {
    prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued prepared packet.selected
    header := packet.header
    aligned := by simpa only [input, metadata] using packet.aligned
    diagnostic := ⟨⟨packet.selected.diagnostics, packet.selected.found, rfl⟩⟩ }
  exact ⟨input, rfl, packet, actual, rfl⟩



theorem ObservedStages.source_of_cached {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : fixture.recipe.compiled.indexed.base.functions[index]? = some named) :
    CallableIndexedNamedGeneration.source named = observed.row.function.typedBody := by
  have length : fixture.recipe.compiled.indexed.base.functions.length = 1 := by
    simpa only [CallableIndexedPreparedInventories.cached_globals, List.length_map] using stages.singletonGlobal
  have before := (List.getElem?_eq_some_iff.mp actual.prepared.selected).1
  have after := (List.getElem?_eq_some_iff.mp selected).1
  rw [length] at before after
  have same : index = actual.prepared.index := by omega
  rw [same, actual.prepared.selected] at selected
  cases Option.some.inj selected
  exact congrArg (fun row => row.function.typedBody) actual.prepared.same

theorem CompiledFixture.no_principal (fixture : CompiledFixture)
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal fixture.recipe.compiled method) : False := by
  obtain ⟨_implementation, _method, _trait, _definition, _substitution, instantiated⟩ := principal.source_instantiation
  cases instantiated with
  | intro _ _ _ _ member _ _ _ _ _ _ _ =>
    simp only [Program.ofChecked, fixture.sameProgram, fixture.methods, List.map_nil,
      List.not_mem_nil] at member

theorem CompiledFixture.signature_member (fixture : CompiledFixture) :
    fixture.signature ∈ fixture.recipe.compiled.sourceProgram.signatures.functions := by
  rw [fixture.sameProgram, fixture.signatures]
  exact .head []

theorem ActualHeader.source {fixture : CompiledFixture} {row : SourceSpecialization.SpecializedFunction}
    (actual : ActualHeader fixture row) : actual.header.function.source = row.function.typedBody := by
  rw [actual.aligned.function]
  exact congrArg (fun row => row.function.typedBody) actual.prepared.same


theorem ActualHeader.body {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) : actual.header.function.body = observed.shape.body := by
  rw [actual.aligned.function]
  change actual.prepared.compilation.statements = [observed.shape.blockNode.id, observed.shape.statement.id]
  have accepted := actual.prepared.compilation.roots
  change (actual.prepared.named.specialized.function.typedBody.roots.mapM _) = _ at accepted
  rw [actual.prepared.same, observed.roots] at accepted
  exact (Except.ok.inj accepted).symm

theorem actualStagePrepared (fixture : CompiledFixture) :
    RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable :=
  RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
    fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected

end Tests.SourceCoreNamedBlock
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedBlockFacts
/-! Finite observations identify all original reads and exclude anonymous code.
They establish compiler coverage without an execution or body-meaning premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreNamedBlock
open Solcore Frontend SourceInference SourceSemantics CoreLowering

theorem ActualHeader.input_types {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.word, .word] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.shape.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    observed.shape.valueScheme, observed.shape.argumentScheme, TypeSystem.Scheme.mono] using inputs.symm

theorem ActualHeader.result_type {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) : actual.header.function.resultType = .word := by
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same]
  exact observed.resultType

theorem ActualHeader.output {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) : actual.header.output = .word := by
  have projected := actual.aligned.projection
  rw [actual.result_type] at projected
  exact (Except.ok.inj projected).symm

def ActualHeader.descriptor {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named actual.header.named.signature.key) := by
  rw [actual.aligned.named, RecursiveNamedPreparedCallEvidence.Prepared.signature_key actual.prepared]
  exact stages.descriptor

theorem ObservedFactory.read_cases {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {id : ExpressionId} {node : ExpressionNode}
    (found : ContainsExpression observed.row.function.typedBody id node) :
    node = observed.shape.initialRead.node ∨ node = observed.shape.localRead.node ∨ node = observed.shape.finalRead.node := by
  have member := found.1
  rw [observed.nodes] at member
  simpa only [FactoryShape.nodeList, List.mem_cons, List.mem_singleton, Node.expression.injEq,
    reduceCtorEq, List.not_mem_nil, false_or, or_false] using member

theorem ObservedFactory.metadata {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    (named : CallableIndexedNamedGeneration.Named) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.MetadataFor
      fixture.recipe.compiled.indexed named observed.row.function.typedBody := by
  apply CallableIndexedOwnedPreparedStagedReadLambdaMetadata.metadata _ named _ observed.noLocals
  intro id node found
  rcases observed.read_cases (lookupExpression?_sound found) with same | same | same
  all_goals subst node
  · exact .inl ⟨_, _, observed.shape.initialRead.form, observed.shape.initialRead.requirements, observed.shape.initialRead.coercions⟩
  · exact .inl ⟨_, _, observed.shape.localRead.form, observed.shape.localRead.requirements, observed.shape.localRead.coercions⟩
  · exact .inl ⟨_, _, observed.shape.finalRead.form, observed.shape.finalRead.requirements, observed.shape.finalRead.coercions⟩

theorem ObservedFactory.no_lambda {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {id : ExpressionId} {node : ExpressionNode}
    (found : ContainsExpression observed.row.function.typedBody id node)
    {parameters result body} (form : node.form = .lambda parameters result body) : False := by
  rcases observed.read_cases found with same | same | same
  all_goals subst node
  · rw [observed.shape.initialRead.form] at form; cases form
  · rw [observed.shape.localRead.form] at form; cases form
  · rw [observed.shape.finalRead.form] at form; cases form

theorem ObservedFactory.value_declaration {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    SourceCoreDataPlaces.rootBinder observed.row.function.typedBody observed.shape.value.id = .ok observed.shape.value := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, observed.inputs,
    observed.nodes, FactoryShape.nodeList, observed.shape.initialRead.form,
    observed.shape.localRead.form, observed.shape.finalRead.form, observed.shape.assignmentForm,
    observed.shape.blockForm, observed.shape.statementForm, observed.shape.initializedForm, observed.shape.valueOwner,
    observed.shape.valueScheme, TypeSystem.Scheme.mono, observed.shape.argumentValue,
    observed.shape.localValue, observed.shape.valueRequirements]

theorem ObservedFactory.local_declaration {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    SourceCoreDataPlaces.rootBinder observed.row.function.typedBody observed.shape.copyBinder.id = .ok observed.shape.copyBinder := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, observed.inputs,
    observed.nodes, FactoryShape.nodeList, observed.shape.initialRead.form,
    observed.shape.localRead.form, observed.shape.finalRead.form, observed.shape.assignmentForm,
    observed.shape.blockForm, observed.shape.statementForm, observed.shape.initializedForm,
    observed.shape.localOwner, observed.shape.localScheme, TypeSystem.Scheme.mono,
    observed.shape.localRequirements,
    Ne.symm observed.shape.localArgument, Ne.symm observed.shape.localValue]

theorem ActualHeader.statements {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) :
    actual.header.function.body = [observed.shape.blockNode.id, observed.shape.statement.id] := actual.body

end Tests.SourceCoreNamedBlock
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedBlockRuntime
/-! Actual public calls allocate a block-local copy and update the outer parameter.
The second call consumes the exact session returned by the first. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreNamedBlock
open Solcore Frontend SourceInference SourceSemantics CoreLowering

def firstInput : Core.Word := Core.Word.ofNatModulo 11
def firstValue : Core.Word := Core.Word.ofNatModulo 12
def secondInput : Core.Word := Core.Word.ofNatModulo 22
def secondValue : Core.Word := Core.Word.ofNatModulo 23

def runOptions : SourceCoreExecution.RunOptions := {
  executionFuel := 100000
  inputValidationFuel := 1000
  outputValidationFuel := 1000 }

structure ObservedCall {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (previous : Core.Word) (value : Core.Word) where
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start observed.row.key [.word previous, .word value] runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion artifact
  executed : session.RunAt observed.row.key [.word previous, .word value] runOptions (.ok (.succeeded completion))
  returned : completion.value = .word value

def observeCall {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (previous : Core.Word) (value : Core.Word) : IO (ObservedCall observed session previous value) := do
  match started : session.start observed.row.key [.word previous, .word value] runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint =>
    let executed ← session.runWithReceipt observed.row.key [.word previous, .word value] runOptions
    match result : executed.val with
    | .error error => throw (IO.userError (reprStr error))
    | .ok (.failed _ _) => throw (IO.userError "named block failed")
    | .ok (.exportError error _) => throw (IO.userError (reprStr error))
    | .ok (.outOfFuel _) => throw (IO.userError "named block exhausted its execution budget")
    | .ok (.succeeded completion) =>
      if returned : completion.value = .word value then
        return ⟨checkpoint, started, completion, result ▸ executed.property, returned⟩
      else throw (IO.userError "named block returned an unexpected Word")

structure ObservedInitial (fixture : CompiledFixture) (observed : ObservedFactory fixture) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facadeCompiled
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  call : ObservedCall observed session firstInput firstValue

def observeInitial (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ObservedInitial fixture observed) := do
  let opened ← fixture.facadeCompiled.openWithReceipt
  let fresh ← opened.val.bootstrapWithExportReceipt
  match ready : fresh.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "named block bootstrap exhausted")
  | .ready session =>
    let call ← observeCall observed session firstInput firstValue
    return ⟨opened.val, opened.property, fresh.val, fresh.property.1, fresh.property.2, session, ready, call⟩

structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedFactory fixture) where
  initial : ObservedInitial fixture observed
  next : ObservedCall observed initial.call.completion.session secondInput secondValue

def observeSequence (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ObservedSequence fixture observed) := do
  let initial ← observeInitial fixture observed
  let next ← observeCall observed initial.call.completion.session secondInput secondValue
  return ⟨initial, next⟩

structure ObservedReceiver (fixture : CompiledFixture) (observed : ObservedFactory fixture) where
  completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics
  registry : completion.result.context.registry = fixture.recipe.compiled.compatible.checked.staticRegistry

theorem initial_receiver (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    Nonempty (ObservedReceiver fixture observed) := by
  obtain ⟨receiver, _entry, registry, issued⟩ :=
    CallableIndexedOwnedPublicFaultReceivers.Receiver.at_registry fixture.recipe.compiled observed.entry
      fixture.recipe.compiled.compatible.checked.staticRegistry (.refl _)
  exact ⟨⟨receiver, issued, registry⟩⟩

private theorem recipe_unique {compiled : SourceCoreExecution.Compiled}
    {first second : SourceCoreIndexedSession.Recipe}
    (left : RecursiveNamedPreparedStageContracts.PublicRecipe compiled first)
    (right : RecursiveNamedPreparedStageContracts.PublicRecipe compiled second) : first = second := by
  cases compiled
  exact Option.some.inj (left.symm.trans right)

theorem ObservedInitial.start_receipt {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (executed : ObservedInitial fixture observed) :
    ∃ (artifact : SourceCoreIndexedSession.Artifact)
      (session : SourceCoreIndexedSession.Session artifact)
      (checkpoint : SourceCoreIndexedSession.Checkpoint artifact)
      (root : SourceCoreIndexedSession.Root fixture.recipe.compiled)
      (world : Core.StoreTyping) (store : Core.Store) (native : Core.Environment)
      (encodedValues : SourceCoreCompatibleValues.Context),
      executed.artifact.IndexedAt fixture.facadeCompiled fixture.recipe artifact ∧
      SourceCoreIndexedSession.Recipe.prepare fixture.recipe.compiled = .ok fixture.recipe ∧
      executed.session.IndexedAt session ∧ executed.call.checkpoint.IndexedAt checkpoint ∧
      RecursiveNamedPublicStartMeaning.StartAt session observed.row.key [.word firstInput, .word firstValue]
        runOptions.inputValidationFuel checkpoint fixture.recipe root world store native encodedValues := by
  obtain ⟨recipe, artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, _program, sessionAt, checkpointAt, started⟩ :=
    RecursiveNamedPublicExecutionMeaning.actual_start fixture.accepted executed.opened executed.call.started
  have same := recipe_unique opened.compiled_recipe fixture.issued
  cases same
  exact ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
    opened, prepared, sessionAt, checkpointAt, started⟩

theorem ObservedInitial.metadata_at_start {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (executed : ObservedInitial fixture observed)
    {artifact : SourceCoreIndexedSession.Artifact} {session : SourceCoreIndexedSession.Session artifact}
    {checkpoint : SourceCoreIndexedSession.Checkpoint artifact}
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {world : Core.StoreTyping} {store : Core.Store} {native : Core.Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (opened : executed.artifact.IndexedAt fixture.facadeCompiled fixture.recipe artifact)
    (sessionAt : executed.session.IndexedAt session)
    (started : RecursiveNamedPublicStartMeaning.StartAt session observed.row.key [.word firstInput, .word firstValue]
      runOptions.inputValidationFuel checkpoint fixture.recipe root world store native encodedValues) :
    encodedValues.registry = fixture.recipe.compiled.compatible.checked.staticRegistry := by
  have ready : executed.bootstrap.ReadyAt 100000 executed.session := .single executed.ready
  obtain ⟨bootstrap, initialized, value, initialStore, _atBootstrap, initial, initializedAt, _done, booted⟩ :=
    ready.indexed opened executed.fresh
  have same : initialized = session := initializedAt.unique sessionAt
  subst initialized
  apply started.simple_registry (booted.registry_at initial)
  intro value member
  rcases List.mem_cons.mp member with same | member
  · exact same ▸ SourceCoreIndexedSession.SimplePublic.word firstInput
  · have same := List.mem_singleton.mp member
    exact same ▸ SourceCoreIndexedSession.SimplePublic.word firstValue

end Tests.SourceCoreNamedBlock
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedBlockSyntax
/-! Original typing supplies the block's initialized local, assignment and
outer return to the actual compiler's static syntax certificate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNamedBlock
open Solcore Frontend SourceInference SourceSemantics CoreLowering

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
  have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  subst actual
  exact original

private theorem returning {source : TypedSource} {context final : SourceSemantics.Context}
    {binder : TypedBinder} {id : StatementId} {node : StatementNode} {facts : StatementFacts}
    {approved : ExpressionId → Prop} {mode : Bool} {rest : List StatementId}
    (unique : NodeOccurrencesUnique source) (read : Read source binder .word)
    (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt (some read.node.id))
    (annotation : node.type = .word) (leaf : approved read.node.id)
    (typed : StatementHasType source {returnType := .word} context id final facts) :
    GenericImperativeMatch.Syntax source approved context (.statements mode (id :: rest)) .word := by
  have original := form_at unique found typed
  rw [form] at original
  cases original with
  | returnValue value =>
      exact .body (.returnValue rest found form annotation read.found read.type
        (by simpa only [read.type] using value) leaf)

private theorem assigned {source : TypedSource} {context : SourceSemantics.Context}
    {binder rhsBinder : TypedBinder} {payload : TypeSystem.Ty} {id : StatementId} {node : StatementNode}
    {assignment : AssignmentResolution} {approved : ExpressionId → Prop} {mode : Bool} {rest : List StatementId}
    (read : Read source rhsBinder payload) (found : source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment .equal read.node.id)
    (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
    (scheme : binder.scheme = .mono payload) (bare : assignment.target.projections = [])
    (targetType : assignment.target.type = payload) (leaf : approved read.node.id)
    (typed : SourceAssignmentHasType source context assignment .equal read.node.id)
    (remaining : GenericImperativeMatch.Syntax source approved context (.statements mode rest) .word) :
    GenericImperativeMatch.Syntax source approved context (.statements mode (id :: rest)) .word := by
  cases typed with
  | wordCompound operator _ _ _ => cases operator
  | equal target rhs _requirements =>
      cases target with
      | intro writable projections target =>
          apply GenericImperativeMatch.Syntax.assign found form
          · intro actual actualFound
            have same := Except.ok.inj (declaration.symm.trans actualFound)
            subst actual
            rw [scheme, bare, targetType]
            exact .nil _
          · intro actual actualFound
            have same := Except.ok.inj (declaration.symm.trans actualFound)
            subst actual
            rw [bare] at projections
            cases projections
            have word := target.symm.trans targetType
            simpa only [word, scheme, TypeSystem.Scheme.mono] using writable
          · simpa only [target] using rhs
          · exact .inl rfl
          · intro child member
            simp only [bare, DataPlaceKeyOrder.sourceKeys, List.mem_cons, List.not_mem_nil, or_false] at member
            subst child
            exact ⟨leaf, read.node, read.found, by simpa only [← target, targetType, read.type] using rhs⟩
          · exact remaining

theorem ObservedFactory.body_shape {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    CallableIndexedOwnedPreparedStagedBranchingTree.Shape observed.row.function.typedBody true observed.shape.body :=
  .block observed.shape.blockFound observed.shape.blockForm
    (.initialized observed.shape.initializedFound observed.shape.initializedForm
      (.assign observed.shape.assignmentFound observed.shape.assignmentForm (.inl rfl) observed.shape.targetBare .nil))
    (.returnValue [] observed.shape.statementFound observed.shape.statementForm)

def ObservedFactory.readIds {fixture : CompiledFixture} (observed : ObservedFactory fixture) : List ExpressionId :=
  [observed.shape.initialRead.node.id, observed.shape.localRead.node.id, observed.shape.finalRead.node.id]

theorem ObservedFactory.body_syntax {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (unique : NodeOccurrencesUnique observed.row.function.typedBody) {approved : ExpressionId → Prop}
    (leaves : ∀ id ∈ observed.readIds, approved id)
    (typed : StatementsHaveType observed.row.function.typedBody {returnType := .word}
      context observed.shape.body final facts) :
    GenericImperativeMatch.Syntax observed.row.function.typedBody approved context
      (.statements true observed.shape.body) .word := by
  have leaf : ∀ id, id ∈ observed.readIds → approved id := leaves
  obtain ⟨middle, headFacts, tailFacts, first, tail⟩ := head_tail typed
  have firstForm := form_at unique observed.shape.blockFound first
  rw [observed.shape.blockForm] at firstForm
  cases firstForm with
  | block innerTyped =>
    apply GenericImperativeMatch.Syntax.block observed.shape.blockFound observed.shape.blockForm observed.shape.blockType
    · obtain ⟨_, _, _, initializedHead, assignedTail⟩ := head_tail innerTyped
      have initialized := form_at unique observed.shape.initializedFound initializedHead
      rw [observed.shape.initializedForm] at initialized
      cases initialized with
      | letInitialized initializer mono extended =>
        apply GenericImperativeMatch.Syntax.initialized observed.shape.initializedFound observed.shape.initializedForm
          observed.local_declaration mono extended
          (by simp [observed.shape.inputs, Ne.symm observed.shape.localValue, Ne.symm observed.shape.localArgument])
          observed.shape.initialRead.found
          (by simp [observed.shape.initialRead.type, observed.shape.localScheme, TypeSystem.Scheme.mono])
          (by simpa only [observed.shape.initialRead.type, observed.shape.localScheme, TypeSystem.Scheme.mono] using initializer)
          (leaf _ (by simp [readIds]))
        obtain ⟨_, _, _, assignedHead, _⟩ := head_tail assignedTail
        have assignment := form_at unique observed.shape.assignmentFound assignedHead
        rw [observed.shape.assignmentForm] at assignment
        cases assignment with
        | assignValue assignmentTyped =>
          exact assigned observed.shape.localRead observed.shape.assignmentFound observed.shape.assignmentForm
            (by rw [observed.shape.targetRoot]; exact observed.value_declaration)
            observed.shape.valueScheme observed.shape.targetBare observed.shape.targetType
            (leaf _ (by simp [readIds])) assignmentTyped (.body (.nil (.inl rfl)))
      | letInitializedGeneralized polymorphic _ _ _ _ =>
        exact False.elim (polymorphic (by simp [observed.shape.localScheme, TypeSystem.Scheme.mono]))
    · obtain ⟨_, _, _, returningHead, _⟩ := head_tail tail
      exact returning unique observed.shape.finalRead observed.shape.statementFound observed.shape.statementForm
        observed.shape.statementType (leaf _ (by simp [readIds])) returningHead

theorem ActualHeader.syntax {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) :
    GenericImperativeMatch.Syntax actual.header.function.source (fun id => ∃ node name binderId,
      actual.header.function.source.lookupExpression? id = some node ∧ node.form = .reference name (.local binderId))
      actual.header.context (.statements true actual.header.function.body) actual.header.function.resultType := by
  obtain ⟨facts, final, typed, _roots, _complete⟩ := actual.aligned.bodyTyped
  rw [actual.source, observed.shape.roots, actual.result_type] at typed
  simp only [List.filterMap_cons, List.filterMap_nil] at typed
  rw [actual.source, actual.body, actual.result_type]
  apply observed.body_syntax (actual.source ▸ actual.header.unique) _ typed
  intro id member
  simp only [ObservedFactory.readIds, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact ⟨_, _, _, observed.shape.initialRead.found, observed.shape.initialRead.form⟩
  · exact ⟨_, _, _, observed.shape.localRead.found, observed.shape.localRead.form⟩
  · exact ⟨_, _, _, observed.shape.finalRead.found, observed.shape.finalRead.form⟩

theorem ActualHeader.branching_receipt {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt actual.header) := by
  apply CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.of_accepted actual.aligned.accepted _ actual.aligned.projection
  rw [actual.source, actual.body]
  exact observed.body_shape

def ActualHeader.branching_body {fixture : CompiledFixture} {row : SourceSpecialization.SpecializedFunction}
    (actual : ActualHeader fixture row)
    (receipt : CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt actual.header) :
    CallableIndexedOwnedPreparedStagedNamedBodies.Body actual.header := {
  row := row, prepared := actual.prepared, instantiation := CallableNamedMetadata.instantiation row
  aligned := actual.aligned, layouts := actual.aligned.layouts, compilation := .branching receipt }

end Tests.SourceCoreNamedBlock
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedBlockSupports
/-! The complete authentic singleton catalog selects the named branching
compiler packet and derives all static children from actual local-read lowering. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreNamedBlock
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body)
open CallableIndexedOwnedPreparedStagedNamedBodiesSupport (Support)

structure StaticSupportPackage (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (registry : SourceCoreRawMetadata.Registry)
    (completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed) where
  input : Input fixture.recipe.compiled
  packet : Issued input
  actual : ActualHeader fixture observed.row
  headerEq : actual.header = packet.header
  rows : Inventory [input]
  rowsEq : rows = .cons packet .nil
  complete : RecursiveNamedCatalogNativeContexts.Complete
    (values := .initial fixture.recipe.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) (headers rows)
  terminals : ∀ header, header ∈ headers rows → Body header
  supports : ∀ header (member : header ∈ headers rows),
    Support (headers rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture))
      (terminals header member) (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
  family : ∀ {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association (headers rows)
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      mapping world function native bindings parameter result),
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor (actualStagePrepared fixture) association
  descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named actual.header.named.signature.key)

 theorem StaticSupportPackage.header_list {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {registry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (support : StaticSupportPackage fixture observed registry completion) : headers support.rows = [support.actual.header] := by
  rw [support.rowsEq, support.headerEq]
  rfl


theorem ActualHeader.support {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row)
    (receipt : CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt actual.header)
    (rootHeaders : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)))
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) rootHeaders)
    {registry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics) :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedBranchingSupport.Support rootHeaders
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry actual.header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) receipt
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  apply Nonempty.intro
  apply CallableIndexedOwnedPreparedNamedBranchingCollectors.of_imperative_compiler actual.prepared actual.aligned
    fixture.recipePrepared actual.diagnostic fixture.source_wellFormed complete (bootstrap_zero fixture.recipe.compiled)
    observed.entryMember receipt
    (CallableIndexedOwnedPreparedNamedBranchingCollectors.operands_of_diagnostic
      actual.prepared actual.aligned actual.diagnostic receiver)
    (CallableIndexedOwnedPreparedNamedBranchingCollectors.unary_of_diagnostic
      actual.prepared actual.aligned actual.diagnostic receiver) _ actual.syntax.prepared
  intro child selected context fields scope fuel id node lowered declarations approved found typed accepted nativeType _native
  obtain ⟨original, name, localId, lookup, form⟩ := approved
  have same := Option.some.inj (found.symm.trans lookup)
  subst original
  obtain ⟨root⟩ := CallableIndexedOwnedPreparedStagedNamedLexicalReadRoots.of_accepted
    actual.prepared actual.aligned actual.diagnostic receiver fixture.source_wellFormed
    (by rw [actual.source]; exact observed.metadata actual.prepared.named)
    ((RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected)
    ((RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).evidence selected) fields
    (by rw [(RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected]; exact declarations)
    (by rw [(RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected]; exact found)
    form
    (by rw [(RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected]; exact typed)
    (by rw [(RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected]; exact accepted)
  exact .recursive root

theorem static_supports (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed) (registry : SourceCoreRawMetadata.Registry)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics) :
    Nonempty (StaticSupportPackage fixture observed registry completion) := by
  obtain ⟨input, _row, packet, actual, sameHeader⟩ := stages.inventory
  let rows : Inventory [input] := .cons packet .nil
  have headerList : headers rows = [actual.header] := by simp only [rows, headers, sameHeader]
  have complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) (headers rows) := by
    rw [headerList]; exact actual.complete stages
  obtain ⟨receipt⟩ := actual.branching_receipt
  let body := actual.branching_body receipt
  obtain ⟨supported⟩ := actual.support receipt (headers rows) complete (registry := registry) receiver
  let terminals : ∀ header, header ∈ headers rows → Body header := fun header member => by
    have same : header = actual.header := by simpa only [headerList, List.mem_singleton] using member
    exact same ▸ body
  have supports : ∀ header (member : header ∈ headers rows),
      Support (headers rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        registry header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture))
        (terminals header member) (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
    intro header member
    have same : header = actual.header := by simpa only [headerList, List.mem_singleton] using member
    subst header
    simpa only [terminals, body, ActualHeader.branching_body, Support] using supported
  have family : ∀ {mapping world function native bindings parameter result}
      (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association (headers rows)
        (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) registry
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
        mapping world function native bindings parameter result),
      CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor (actualStagePrepared fixture) association := by
    intro mapping world function native bindings parameter result association
    cases association with
    | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
      have found := code.sourceFound
      rw [support.source.trans (stages.source_of_cached actual support.caller.selected)] at found
      exact False.elim (observed.no_lambda (lookupExpression?_sound found) code.sourceForm)
    | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
      exact False.elim (fixture.no_principal support.principal)
  exact ⟨{
    input := input
    packet := packet
    actual := actual
    headerEq := sameHeader
    rows := rows
    rowsEq := rfl
    complete := complete
    terminals := terminals
    supports := supports
    family := family
    descriptor := actual.descriptor stages }⟩

end Tests.SourceCoreNamedBlock
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedBlockCommon
/-! Retained callers connect the exact sessions and Source heaps of both named calls. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreNamedBlock
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open RecursiveNamedPublicFunctionHistory (Entry)

abbrev PublicSupports {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (receiver : ObservedReceiver fixture observed) :=
  StaticSupportPackage fixture observed receiver.completion.result.context.registry receiver.completion

def PublicSupports.functions {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :=
  CallableIndexedOwnedContextualCellOrigins.functions (headers support.rows)
    (keys fixture.recipe.compiled) receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics) observed.profile

theorem PublicSupports.observations {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :
    CompatibleEquality.FunctionObservations fixture.recipe.compiled.compatible.checked.catalog
      support.functions (CallableIndexedLambdaValues.Identity fixture.recipe.compiled.indexed) := by
  intro metadata mapping world sourceType source native type origin
  exact CallableIndexedOwnedGeneralLambdaValues.observations _ receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
    observed.profile (registry := metadata)
    (CallableIndexedOwnedContextualCellOrigins.functions_include_general observed.profile origin)

structure RetainedState {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {publicArtifact : SourceCoreExecution.Artifact} (publicSession : SourceCoreExecution.Session publicArtifact)
    (entries : List Entry) where
  artifact : SourceCoreIndexedSession.Artifact
  session : SourceCoreIndexedSession.Session artifact
  mapping : GeneralHeap.LocationMap
  world : Core.StoreTyping
  heap : Dynamic.Heap
  store : Core.Store
  caller : RecursiveNamedPublicFunctionHistory.Caller (headers support.rows)
    (keys fixture.recipe.compiled) mapping world heap store
  atSession : publicSession.IndexedAt session
  atRecipe : RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact fixture.recipe
  receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    receiving.entry receiving.result.context.registry receiving.result.extension receiving.result.diagnostics
  extension : SourceCoreRawMetadata.Extends receiver.completion.result.context.registry receiving.result.context.registry
  registry : session.RegistryAt receiving.result.context.registry
  history : RecursiveNamedPublicFunctionHistory.History (headers support.rows)
    (keys fixture.recipe.compiled) support.functions receiving.result.context.registry
    support.actual.header session mapping world heap store caller entries

def SourceCall {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (arguments : List Dynamic.Value)
    (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ rawD function size,
    CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD function ∧
    Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) size invocation
      support.actual.header.function.context before (.global function) arguments outcome after

end Tests.SourceCoreNamedBlock
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedBlockSeed
/-! The initial block call derives its Source trace, Word result and reusable
empty history from actual bootstrap, input encoding and public completion. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNamedBlock
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

theorem first_meaning {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed}
    (support : PublicSupports receiver) (stages : ObservedStages fixture observed)
    (first : ObservedInitial fixture observed) :
    ∃ state : RetainedState support first.call.completion.session [],
      SourceCall support support.actual.header
        (RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function)
        ⟨[]⟩ [.word firstInput, .word firstValue] (.value (.word firstValue)) state.heap := by
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree fixture.recipe.compiled receiver.issued)
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ := first.start_receipt
  have startupRegistry := first.metadata_at_start opened sessionAt started
  obtain ⟨selectedHeader, selected⟩ := started.selection prepared support.complete
  have selectedEq : selectedHeader = support.actual.header := by
    have member := selected.member
    rw [support.header_list] at member
    exact List.mem_singleton.mp member
  subst selectedHeader
  have inputs : RecursiveNamedPublicNestedInputs.Inputs support.rows session support.actual.header.function.context
      (support.actual.header.bindings.map (fun binding => binding.1.scheme.body))
      [.word firstInput, .word firstValue] [.word firstInput, .word firstValue] := by
    rw [support.actual.input_types]
    exact .cons (.leaf (.data
      ⟨.word firstInput, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word firstInput⟩
      ⟨.word firstInput, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word firstInput⟩))
      (.cons (.leaf (.data
        ⟨.word firstValue, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word firstValue⟩
        ⟨.word firstValue, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word firstValue⟩)) .nil)
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiver.completion.result.context.registry := by
    rw [startupRegistry]
    exact receiver.completion.result.extension
  have sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt support.actual.header support.input.prepared.available
      (CallableNamedReversal.global (CallableNamedMetadata.global support.packet.header.named.specialized support.input.prepared.available)) := by
    rw [support.headerEq]
    exact support.packet.sourceAt
  obtain ⟨caller, actual, generation, value, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, result,
      returnedCaller, added, handles, _related, retained⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedHistoryPublicSeed.public_run_succeeded_collects
      (inputs := [support.input]) (rows := support.rows) (distinct := by simp)
      (stagePrepared := actualStagePrepared fixture) (receiver := receiver.issued)
      (profile := observed.profile) (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := support.terminals) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := prepared) (selected := selected)
      (opened := opened) (fresh := first.fresh) (ready := .single first.ready)
      (sameRuntime := SourceCoreExecution.Session.SameRuntime.refl first.session) (atSession := sessionAt)
      (atCheckpoint := checkpointAt) (started := started) (inputReceipts := inputs)
      (metadata := metadata) (sourceAt := sourceAt)
      (invocation := RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function)
      first.call.started first.call.executed .skip support.descriptor
  have empty : added = [] := List.map_eq_nil_iff.mp handles
  subst added
  have returnedRegistry := started.returned_registry succeeded
  rw [startupRegistry] at returnedRegistry
  have atRecipe : artifact.RecipeAt fixture.recipe := by
    cases artifact
    exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2
  rw [resultType, support.actual.result_type] at requested
  have outcomeValue := RecursiveNamedPublicWordResultMeaning.result_word succeeded requested
    (valueEq.symm.trans first.call.returned) support.actual.output result
  let state : RetainedState support first.call.completion.session [] := {
    artifact := artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := returnedCaller
    atSession := returnedAt
    atRecipe := started.recipe_eq
    receiving := receiver.completion
    issued := receiver.issued
    extension := .refl _
    registry := receiver.registry.symm ▸ returnedRegistry
    history := retained }
  exact ⟨state, support.input.prepared.available, _, sourceSize, sourceAt, outcomeValue ▸ trace⟩

end Tests.SourceCoreNamedBlock
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedBlockStep
/-! The following block call starts from the exact session and heap reached by the first call. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNamedBlock
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

theorem RetainedState.update {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (state : RetainedState support session []) {previous : Core.Word} {value : Core.Word}
    (call : ObservedCall observed session previous value) (invocation : Staging.Recursive.Scope) :
    ∃ after : RetainedState support call.completion.session [],
      SourceCall support support.actual.header invocation state.heap [.word previous, .word value]
        (.value (.word value)) after.heap := by
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree fixture.recipe.compiled receiver.issued)
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.input] support.rows support.complete
    state.atRecipe state.history.current.1 state.atSession call.started
  have selectedHeader : request.header = support.actual.header := by
    have singleton : ∀ header, header ∈ headers support.rows → header = support.actual.header := by
      intro header member
      rw [support.header_list] at member
      exact List.mem_singleton.mp member
    exact singleton _ request.selected.member
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs [] request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [.word previous, .word value] [.word previous, .word value] := by
    rw [selectedHeader, support.actual.input_types]
    exact .cons (.data ⟨.word previous, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word previous⟩
      ⟨.word previous, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word previous⟩)
      (.cons (.data ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩
        ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩) .nil)
  have registry := request.started.simple_registry state.registry (by
    intro publicValue member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .word previous
    · exact .word value)
  have metadata : SourceCoreRawMetadata.Extends request.encodedValues.registry state.receiving.result.context.registry := by
    rw [registry]; exact .refl _
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selectedHeader]; exact support.descriptor
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨actual, generation, native, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, result,
      reached, _related, retained⟩ :=
    CallableIndexedOwnedPreparedStagedHistoryPublicContinuations.public_run_succeeded_retains
      (inputs := [support.input]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture) (completion := state.receiving)
      (receiver := state.issued) (profile := observed.profile) (observations := support.observations)
      (extension := state.receiving.result.extension) (semantic := semantic)
      (family := support.family) (namedTerminals := support.terminals) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := fixture.recipePrepared)
      (selected := request.selected) (caller := state.caller) (history := state.history)
      (atCheckpoint := request.atCheckpoint) (started := request.started)
      (inputReceipts := inputs) (metadata := metadata) (sourceAt := request.sourceAt)
      (invocation := invocation) call.started call.executed descriptor
  have atRecipe : state.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType, selectedHeader, support.actual.result_type] at requested
  have outcomeValue := RecursiveNamedPublicWordResultMeaning.result_word succeeded requested
    (valueEq.symm.trans call.returned) (by rw [selectedHeader]; exact support.actual.output) result
  have returnedRegistry := request.started.returned_registry succeeded
  rw [registry] at returnedRegistry
  let next : RetainedState support call.completion.session [] := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := returnedAt
    atRecipe := state.atRecipe
    receiving := state.receiving
    issued := state.issued
    extension := state.extension
    registry := returnedRegistry
    history := retained }
  refine ⟨next, request.rawD, request.function, sourceSize, ?_, ?_⟩
  · rw [← selectedHeader]; exact request.sourceAt
  · simpa only [outcomeValue] using trace

end Tests.SourceCoreNamedBlock
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedBlockInitialForward
/-! The independent nonempty-loop trace determines both public fuel bounds at its
original checkpoint. Every sufficient resume returns Word11 and the same heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNamedBlock
open Solcore Frontend SourceInference SourceSemantics CoreLowering

/-- The initial entry exports its genuine raw result type and returns the exact
Source heap in a reusable session at every sufficient pair of fuel budgets. -/
def InitialForwardAt {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (first : ObservedInitial fixture observed) (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome first.artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      first.call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion first.artifact,
        outcome = .succeeded completion ∧
        completion.value = .word firstValue ∧
        completion.session.ExportsReady ∧
        ∃ returned : RetainedState support completion.session [], returned.heap = after

theorem forward_initial {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (first : ObservedInitial fixture observed)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}
    (trace : SourceCall support support.actual.header invocation ⟨[]⟩ [.word firstInput, .word firstValue] (.value (.word firstValue)) after) :
    InitialForwardAt support first after := by
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree fixture.recipe.compiled receiver.issued)
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ := first.start_receipt
  obtain ⟨selectedHeader, selected⟩ := started.selection prepared support.complete
  have selectedEq : selectedHeader = support.actual.header := by
    have member := selected.member
    rw [support.header_list] at member
    exact List.mem_singleton.mp member
  subst selectedHeader
  have inputs : RecursiveNamedPublicNestedInputs.Inputs support.rows session support.actual.header.function.context
      (support.actual.header.bindings.map (fun binding => binding.1.scheme.body)) [.word firstInput, .word firstValue] [.word firstInput, .word firstValue] := by
    rw [support.actual.input_types]
    exact .cons (.leaf (.data
      ⟨.word firstInput, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word firstInput⟩
      ⟨.word firstInput, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word firstInput⟩))
      (.cons (.leaf (.data
        ⟨.word firstValue, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word firstValue⟩
        ⟨.word firstValue, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word firstValue⟩)) .nil)
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  obtain ⟨receiving, contextAt, issued, extended, _diagnostics, _caller, _capture,
      _payload, _finalStore, _finalMap, _finalWorld, requiredExecution, requiredOutput,
      _nativeEnough, _fullResult, publicEnough⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedOutputPreservation.public_resume_has_sufficient_fuel
      (inputs := [support.input]) (rows := support.rows) (distinct := by simp)
      (stagePrepared := actualStagePrepared fixture) (receiver := receiver.issued)
      (profile := observed.profile) (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (baseRegistry := receiver.registry)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := support.terminals)
      (namedSupport := support.supports) (wellFormed := fixture.source_wellFormed)
      (prepared := prepared) (selected := selected) (opened := opened)
      (fresh := first.fresh) (ready := .single first.ready) (authority := first.authority)
      (atSession := sessionAt) (atCheckpoint := checkpointAt) (started := started)
      (inputReceipts := inputs) (sourceAt := sourceAt) applied
  have atRecipe : artifact.RecipeAt fixture.recipe := by
    cases artifact
    exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  have rawResult := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2
  rw [rawResult, support.actual.result_type] at requested
  have nativeWord : _payload = .word firstValue := by
    have represented := _fullResult.2.1
    rw [support.actual.output] at represented
    cases represented with
    | value related =>
      obtain ⟨word, same, native⟩ := CompatibleExpressionPrimitives.word_fields related
      exact native.trans (congrArg Core.Value.word (Dynamic.Value.word.inj same).symm)
  refine ⟨requiredExecution, requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, _generation, reached, succeeded, exported, actualAt,
      _related, history, registry, ready⟩ :=
    publicEnough executionFuel outputFuel outcome executionBound outputBound resumed
  let returned : RetainedState support completion.session [] := {
    artifact := artifact
    session := actual.session
    mapping := _finalMap
    world := _finalWorld
    heap := after
    store := _finalStore
    caller := reached
    atSession := actualAt.2.2.2
    atRecipe := started.recipe_eq
    receiving := receiving
    issued := issued
    extension := extended
    registry := (congrArg (·.registry) contextAt).symm ▸ registry
    history := history }
  exact ⟨completion, succeeded, actualAt.1.trans ((nativeWord ▸ exported).word_value requested),
    actualAt.2.2.2.exportsReady_iff.mpr ready, returned, rfl⟩


end Tests.SourceCoreNamedBlock
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedBlockForward
/-! Following named execution derives sufficient public fuel from the independent
Source trace at the exact retained heap. The output and next history follow for
every sufficient resume of the original checkpoint. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNamedBlock
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

def ForwardAt {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {previous : Core.Word} {value : Core.Word} (call : ObservedCall observed session previous value)
    (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion artifact,
        outcome = .succeeded completion ∧ completion.value = .word value ∧
        completion.session.ExportsReady ∧
        ∃ returned : RetainedState support completion.session [], returned.heap = after

theorem forward_update {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (state : RetainedState support session []) {previous : Core.Word} {value : Core.Word}
    (call : ObservedCall observed session previous value) (ready : session.ExportsReady)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}
    (trace : SourceCall support support.actual.header invocation state.heap
      [.word previous, .word value] (.value (.word value)) after) :
    ForwardAt support call after := by
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree fixture.recipe.compiled receiver.issued)
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.input] support.rows support.complete
    state.atRecipe state.history.current.1 state.atSession call.started
  have selectedHeader : request.header = support.actual.header := by
    have singleton : ∀ header, header ∈ headers support.rows → header = support.actual.header := by
      intro header member
      rw [support.header_list] at member
      exact List.mem_singleton.mp member
    exact singleton _ request.selected.member
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs [] request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [.word previous, .word value] [.word previous, .word value] := by
    rw [selectedHeader, support.actual.input_types]
    exact .cons (.data ⟨.word previous, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word previous⟩
      ⟨.word previous, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word previous⟩)
      (.cons (.data ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩
        ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩) .nil)
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  have sourceAt' : CallableIndexedOwnedFunctionValues.NamedSourceAt request.header rawD function := by
    rw [selectedHeader]; exact sourceAt
  obtain ⟨receiving, contextAt, issued, extended, _diagnostics, _capture,
      payload, finalStore, finalMap, finalWorld, requiredExecution, requiredOutput,
      _nativeEnough, fullResult, publicEnough⟩ :=
    RecursiveNamedPublicActualRegistryNamedOutputPreservation.public_resume_has_sufficient_fuel
      (inputs := [support.input]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture) (completion := state.receiving)
      (receiver := state.issued) (profile := observed.profile) (observations := support.observations)
      (semantic := semantic) (family := support.family)
      (namedTerminals := support.terminals) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := fixture.recipePrepared)
      (selected := request.selected) (caller := state.caller) (history := state.history)
      (atCheckpoint := request.atCheckpoint) (started := request.started)
      (inputReceipts := inputs) (atRegistry := state.registry)
      (exportsReady := state.atSession.exportsReady_iff.mp ready) (sourceAt := sourceAt') applied
  have atRecipe : state.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType, selectedHeader, support.actual.result_type] at requested
  have nativeWord : payload = .word value := by
    have represented := fullResult.2.1
    rw [selectedHeader, support.actual.output] at represented
    cases represented with
    | value related =>
      obtain ⟨word, same, native⟩ := CompatibleExpressionPrimitives.word_fields related
      exact native.trans (congrArg Core.Value.word (Dynamic.Value.word.inj same).symm)
  refine ⟨requiredExecution, requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, _generation, reached, succeeded, exported, actualAt,
      _related, history, registry, returnedReady⟩ :=
    publicEnough executionFuel outputFuel outcome executionBound outputBound resumed
  let returned : RetainedState support completion.session [] := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := actualAt.2.2.2
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := state.extension.trans extended
    registry := (congrArg (·.registry) contextAt).symm ▸ registry
    history := history }
  exact ⟨completion, succeeded, actualAt.1.trans ((nativeWord ▸ exported).word_value requested),
    actualAt.2.2.2.exportsReady_iff.mpr returnedReady, returned, rfl⟩

end Tests.SourceCoreNamedBlock
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedBlockPublicExecution
/-! An independently checked and compiled named block allocates a local and
mutates an outer parameter through two public calls. Its real returned session carries the first
heap into the second call; each Source trace also entails sufficient public
execution and output fuel at that call's original checkpoint. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNamedBlock
open Solcore Frontend SourceInference SourceSemantics CoreLowering

theorem closed_sequence_meaning (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed) (sequence : ObservedSequence fixture observed) :
    ∃ (receiver : ObservedReceiver fixture observed) (support : PublicSupports receiver)
      (first : RetainedState support sequence.initial.call.completion.session [])
      (second : RetainedState support sequence.next.completion.session []),
      SourceCall support support.actual.header
        (RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function)
        ⟨[]⟩ [.word firstInput, .word firstValue] (.value (.word firstValue)) first.heap ∧
      SourceCall support support.actual.header
        (RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function)
        first.heap [.word secondInput, .word secondValue] (.value (.word secondValue)) second.heap ∧
      InitialForwardAt support sequence.initial first.heap ∧
      ForwardAt support sequence.next second.heap := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  obtain ⟨support⟩ := static_supports fixture observed stages receiver.completion.result.context.registry receiver.issued
  obtain ⟨first, initialTrace⟩ := first_meaning support stages sequence.initial
  obtain ⟨second, nextTrace⟩ := first.update sequence.next
    (RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function)
  have initialReady : sequence.initial.session.ExportsReady :=
    (show sequence.initial.bootstrap.ReadyAt 100000 sequence.initial.session from .single sequence.initial.ready).exportsReady
      sequence.initial.authority
  have firstReady := sequence.initial.call.executed.exportsReady initialReady
  exact ⟨receiver, support, first, second, initialTrace, nextTrace,
    forward_initial support sequence.initial initialTrace,
    forward_update first sequence.next firstReady nextTrace⟩

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeFactory fixture
  let stages ← observeStages fixture observed
  let sequence ← observeSequence fixture observed
  have _meaning := closed_sequence_meaning fixture observed stages sequence
  IO.println "Actual named block: (11,12)->12 then (22,23)->23, exact Source histories and sufficient public fuel for both calls proved"

end Tests.SourceCoreNamedBlock
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedBranchFixture
/-! Actual compilation, selected inventory and static branch observations for
one named Bool/Word function with a scoped local and returning branches. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreNamedBranch
open Solcore Frontend SourceInference SourceSemantics

private def observeFact (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

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
  let signature :: _ := checked.program.signatures.functions
    | throw (IO.userError "factory signature missing")
  let seeds := [SourceCompiler.Seed.declaration signature.id]
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

structure ObservedFactory (fixture : CompiledFixture) where
  row : SourceSpecialization.SpecializedFunction
  shape : FactoryShape row.function fixture.signature
  member : row ∈ fixture.recipe.compiled.validationPlan.specializations
  sourceOwner : row.function.typedBody.owner = fixture.signature.id
  parameters : row.parameterSubstitution = []
  closed : row.assumptions = []
  ordinary : row.function.returnComptime = false
  resultType : row.function.inferredBodyType = .word
  target : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
    (CallableNamedMetadata.instantiation row) = .ok row.key
  nodes : row.function.typedBody.nodes = shape.nodeList
  noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []
  profile : fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true
  entry : SourceCoreCallableIndexedPrograms.Entry fixture.recipe.compiled.indexed.layouts
  entryMember : entry ∈ fixture.recipe.compiled.indexed.entries

abbrev ObservedFactory.inputs {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.inputs
abbrev ObservedFactory.roots {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.roots
abbrev ObservedFactory.flag {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.flag
abbrev ObservedFactory.argument {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.argument
abbrev ObservedFactory.binderScheme {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.argumentScheme

private def observeTarget (fixture : CompiledFixture) (row : SourceSpecialization.SpecializedFunction) :
    IO (PLift (SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) = .ok row.key)) := do
  match accepted : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) with
  | .error error => throw (IO.userError (reprStr error))
  | .ok key =>
    let ⟨same⟩ ← observeFact (key = row.key) "captured factory exact key"
    return ⟨by rw [accepted, same]⟩

def observeFactory (fixture : CompiledFixture) : IO (ObservedFactory fixture) := do
  match rows : fixture.recipe.compiled.validationPlan.specializations with
  | [row] =>
    let shape ← observeShape row.function fixture.signature
    match entries : fixture.recipe.compiled.indexed.entries with
    | [entry] =>
      let ⟨sourceOwner⟩ ← observeFact (row.function.typedBody.owner = fixture.signature.id) "named branch source owner"
      let ⟨parameters⟩ ← observeFact (row.parameterSubstitution = []) "named branch substitution"
      let ⟨closed⟩ ← observeFact (row.assumptions = []) "named branch assumptions"
      let ⟨resultType⟩ ← observeFact (row.function.inferredBodyType = .word) "named branch result type"
      let ⟨ordinary⟩ ← observeFact (row.function.returnComptime = false) "named branch ordinary result"
      let ⟨target⟩ ← observeTarget fixture row
      let ⟨nodes⟩ ← observeFact (row.function.typedBody.nodes = shape.nodeList) "named branch nodes"
      let ⟨noLocals⟩ ← observeFact (fixture.recipe.compiled.indexed.base.locals.bindings = []) "named branch local catalog"
      let ⟨profile⟩ ← observeFact (fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true) "named branch profile"
      return {
        row, shape, sourceOwner, parameters, closed, ordinary, resultType, target, nodes, noLocals, profile, entry
        member := by rw [rows]; exact .head []
        entryMember := by rw [entries]; exact .head [] }
    | _ => throw (IO.userError "named branch entry count")
  | _ => throw (IO.userError "named branch specialization count")

/-- The staged selection is obtained from the retained callable table and
original sidecar of the concrete compiler result. -/
structure ObservedStages (fixture : CompiledFixture)
    (observed : ObservedFactory fixture) where
  singletonGlobal : fixture.recipe.compiled.indexed.base.globals.length = 1
  descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named observed.row.key)
  native : SourceCoreGeneralFunctions.CallableContext
  present : fixture.recipe.compiled.indexed.base.callableContext = some native
  sidecar : SourceCoreStageContracts.Sidecar
  issued : SourceCoreStageContracts.prepareSidecar
    fixture.recipe.compiled.indexed.base.plan observed.row.key = .ok sidecar

def observeStages (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ObservedStages fixture observed) := do
  match present : fixture.recipe.compiled.indexed.base.callableContext with
  | none => throw (IO.userError "factory callable context missing")
  | some native =>
    match issued : SourceCoreStageContracts.prepareSidecar
        fixture.recipe.compiled.indexed.base.plan observed.row.key with
    | .error _ => throw (IO.userError "factory original sidecar missing")
    | .ok sidecar =>
      if singletonGlobal : fixture.recipe.compiled.indexed.base.globals.length = 1 then
        match SourceCoreCallableContracts.descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
            (.named observed.row.key) with
        | .error error => throw (IO.userError (reprStr error))
        | .ok descriptor => return ⟨singletonGlobal, descriptor, native, present, sidecar, issued⟩
      else throw (IO.userError "factory global count")

def ObservedStages.registry {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (_actual : ObservedStages fixture observed) : Staging.Recursive.Registry :=
  RecursiveNamedPreparedStageScopes.registry
    (RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected)

theorem ObservedStages.selected {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    stages.registry.Closure actual.header.function
      (RecursiveStageRegistry.scope stages.sidecar [] actual.header.function) := by
  have same := RecursiveNamedPreparedStageScopes.sidecar_caller stages.issued
    (CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.record actual.prepared actual.aligned)
  rw [actual.aligned.function]
  exact RecursiveNamedPreparedStageScopes.Selected.named actual.prepared stages.sidecar stages.issued same


theorem ActualHeader.complete {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [actual.header] := by
  have selected := CallableIndexedPreparedInventories.cached_global_at fixture.recipe.compiled actual.prepared.selected
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  rw [stages.singletonGlobal] at bound
  have zero : actual.prepared.index = 0 := by omega
  intro index signature found
  have bound := (List.getElem?_eq_some_iff.mp found).1
  rw [stages.singletonGlobal] at bound
  have indexZero : index = 0 := by omega
  refine ⟨actual.header, .head [], actual.aligned.slot.trans (zero.trans indexZero.symm), ?_⟩
  rw [actual.aligned.named]
  rw [zero] at selected
  rw [indexZero] at found
  exact Option.some.inj (selected.symm.trans found)

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


theorem ObservedStages.inventory {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) :
    ∃ input : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled,
      input.row = observed.row ∧
      ∃ packet : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued input,
      ∃ actual : ActualHeader fixture observed.row, actual.header = packet.header := by
  obtain ⟨prepared⟩ := fixture.prepared observed.member
  have range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures fixture.recipe.compiled.sourceProgram.signatures) observed.row.parameterSubstitution := by
    simp only [observed.parameters, SourceSemantics.ParameterSubstitution.RangeWellFormed,
      List.not_mem_nil, false_implies, implies_true]
  have metadata : CallableNamedCanonicalOrder.retainedInstantiation observed.row =
      CallableNamedMetadata.instantiation observed.row := by
    simp [CallableNamedCanonicalOrder.retainedInstantiation, CallableNamedMetadata.instantiation, observed.parameters]
  have target : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedCanonicalOrder.retainedInstantiation observed.row) = .ok prepared.named.signature.key := by
    rw [metadata, RecursiveNamedPreparedCallEvidence.Prepared.signature_key prepared]
    exact observed.target
  have selected := CallableIndexedPreparedInventories.cached_global_at fixture.recipe.compiled prepared.selected
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  rw [stages.singletonGlobal] at bound
  have zero : prepared.index = 0 := by omega
  have globals : fixture.recipe.compiled.indexed.base.globals = [prepared.named.signature] := by
    obtain ⟨first, single⟩ := List.length_eq_one_iff.mp stages.singletonGlobal
    rw [single, zero] at selected
    have same : first = prepared.named.signature := by simpa only [List.getElem?_cons_zero, Option.some.injEq] using selected
    exact single.trans (congrArg (fun value => [value]) same)
  let input : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled := {
    row := observed.row
    prepared := prepared
    range := range
    ordinaryReturn := observed.ordinary
    ordinaryParameters := by
      intro binder member
      rw [observed.inputs] at member
      rcases List.mem_cons.mp member with same | rest
      · exact same ▸ observed.shape.flagOrdinary
      · have same := List.mem_singleton.mp rest
        exact same ▸ observed.shape.argumentOrdinary
    target := target
    slot := by simp only [CallableNamedMetadata.Slot, globals, zero]; simp }
  obtain ⟨packet⟩ := CallableIndexedOwnedPreparedFiniteNamedInventories.issue fixture.source_wellFormed input
  let actual : ActualHeader fixture observed.row := {
    prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued prepared packet.selected
    header := packet.header
    aligned := by simpa only [input, metadata] using packet.aligned
    diagnostic := ⟨⟨packet.selected.diagnostics, packet.selected.found, rfl⟩⟩ }
  exact ⟨input, rfl, packet, actual, rfl⟩



theorem ObservedStages.source_of_cached {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : fixture.recipe.compiled.indexed.base.functions[index]? = some named) :
    CallableIndexedNamedGeneration.source named = observed.row.function.typedBody := by
  have length : fixture.recipe.compiled.indexed.base.functions.length = 1 := by
    simpa only [CallableIndexedPreparedInventories.cached_globals, List.length_map] using stages.singletonGlobal
  have before := (List.getElem?_eq_some_iff.mp actual.prepared.selected).1
  have after := (List.getElem?_eq_some_iff.mp selected).1
  rw [length] at before after
  have same : index = actual.prepared.index := by omega
  rw [same, actual.prepared.selected] at selected
  cases Option.some.inj selected
  exact congrArg (fun row => row.function.typedBody) actual.prepared.same

theorem CompiledFixture.no_principal (fixture : CompiledFixture)
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal fixture.recipe.compiled method) : False := by
  obtain ⟨_implementation, _method, _trait, _definition, _substitution, instantiated⟩ := principal.source_instantiation
  cases instantiated with
  | intro _ _ _ _ member _ _ _ _ _ _ _ =>
    simp only [Program.ofChecked, fixture.sameProgram, fixture.methods, List.map_nil,
      List.not_mem_nil] at member

theorem CompiledFixture.signature_member (fixture : CompiledFixture) :
    fixture.signature ∈ fixture.recipe.compiled.sourceProgram.signatures.functions := by
  rw [fixture.sameProgram, fixture.signatures]
  exact .head []

theorem ActualHeader.source {fixture : CompiledFixture} {row : SourceSpecialization.SpecializedFunction}
    (actual : ActualHeader fixture row) : actual.header.function.source = row.function.typedBody := by
  rw [actual.aligned.function]
  exact congrArg (fun row => row.function.typedBody) actual.prepared.same


theorem ActualHeader.body {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) : actual.header.function.body = observed.shape.body := by
  rw [actual.aligned.function]
  change actual.prepared.compilation.statements = [observed.shape.branch.id]
  have accepted := actual.prepared.compilation.roots
  change (actual.prepared.named.specialized.function.typedBody.roots.mapM _) = _ at accepted
  rw [actual.prepared.same, observed.roots] at accepted
  exact (Except.ok.inj accepted).symm

theorem actualStagePrepared (fixture : CompiledFixture) :
    RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable :=
  RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
    fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected

end Tests.SourceCoreNamedBranch
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedBranchFacts
/-! Finite observations identify all original reads and exclude anonymous code.
They establish compiler coverage without an execution or body-meaning premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreNamedBranch
open Solcore Frontend SourceInference SourceSemantics CoreLowering

theorem ActualHeader.input_types {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.bool, .word] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.shape.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    observed.shape.flagScheme, observed.shape.argumentScheme, TypeSystem.Scheme.mono] using inputs.symm

theorem ActualHeader.result_type {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) : actual.header.function.resultType = .word := by
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same]
  exact observed.resultType

theorem ActualHeader.output {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) : actual.header.output = .word := by
  have projected := actual.aligned.projection
  rw [actual.result_type] at projected
  exact (Except.ok.inj projected).symm

def ActualHeader.descriptor {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named actual.header.named.signature.key) := by
  rw [actual.aligned.named, RecursiveNamedPreparedCallEvidence.Prepared.signature_key actual.prepared]
  exact stages.descriptor

theorem ObservedFactory.read_cases {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {id : ExpressionId} {node : ExpressionNode}
    (found : ContainsExpression observed.row.function.typedBody id node) :
    node = observed.shape.conditionRead.node ∨ node = observed.shape.initialRead.node ∨
      node = observed.shape.localRead.node ∨ node = observed.shape.elseRead.node := by
  have member := found.1
  rw [observed.nodes] at member
  simpa only [FactoryShape.nodeList, List.mem_cons, List.mem_singleton, Node.expression.injEq,
    reduceCtorEq, List.not_mem_nil, false_or, or_false] using member

theorem ObservedFactory.metadata {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    (named : CallableIndexedNamedGeneration.Named) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.MetadataFor
      fixture.recipe.compiled.indexed named observed.row.function.typedBody := by
  apply CallableIndexedOwnedPreparedStagedReadLambdaMetadata.metadata _ named _ observed.noLocals
  intro id node found
  rcases observed.read_cases (lookupExpression?_sound found) with same | same | same | same
  all_goals subst node
  · exact .inl ⟨_, _, observed.shape.conditionRead.form, observed.shape.conditionRead.requirements, observed.shape.conditionRead.coercions⟩
  · exact .inl ⟨_, _, observed.shape.initialRead.form, observed.shape.initialRead.requirements, observed.shape.initialRead.coercions⟩
  · exact .inl ⟨_, _, observed.shape.localRead.form, observed.shape.localRead.requirements, observed.shape.localRead.coercions⟩
  · exact .inl ⟨_, _, observed.shape.elseRead.form, observed.shape.elseRead.requirements, observed.shape.elseRead.coercions⟩

theorem ObservedFactory.no_lambda {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {id : ExpressionId} {node : ExpressionNode}
    (found : ContainsExpression observed.row.function.typedBody id node)
    {parameters result body} (form : node.form = .lambda parameters result body) : False := by
  rcases observed.read_cases found with same | same | same | same
  all_goals subst node
  · rw [observed.shape.conditionRead.form] at form; cases form
  · rw [observed.shape.initialRead.form] at form; cases form
  · rw [observed.shape.localRead.form] at form; cases form
  · rw [observed.shape.elseRead.form] at form; cases form

theorem ObservedFactory.local_declaration {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    SourceCoreDataPlaces.rootBinder observed.row.function.typedBody observed.shape.copyBinder.id =
      .ok observed.shape.copyBinder := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders,
    observed.shape.inputs, observed.nodes, FactoryShape.nodeList,
    observed.shape.conditionRead.form, observed.shape.initialRead.form, observed.shape.localRead.form,
    observed.shape.elseRead.form, observed.shape.initializedForm, observed.shape.thenReturnForm,
    observed.shape.elseReturnForm, observed.shape.branchForm, observed.shape.localOwner,
    observed.shape.localScheme, TypeSystem.Scheme.mono, observed.shape.localRequirements,
    Ne.symm observed.shape.localFlag, Ne.symm observed.shape.localArgument]

theorem ActualHeader.statements {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) :
    actual.header.function.body = [observed.shape.branch.id] := by
  rw [actual.aligned.function]
  change actual.prepared.compilation.statements = _
  have accepted := actual.prepared.compilation.roots
  change (actual.prepared.named.specialized.function.typedBody.roots.mapM _) = _ at accepted
  rw [actual.prepared.same, observed.shape.roots] at accepted
  exact (Except.ok.inj accepted).symm

end Tests.SourceCoreNamedBranch
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedBranchRuntime
/-! Actual public calls enter both arms of the accepted named conditional.
The second call consumes the exact session returned by the first. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreNamedBranch
open Solcore Frontend SourceInference SourceSemantics CoreLowering

def firstValue : Core.Word := Core.Word.ofNatModulo 11
def secondValue : Core.Word := Core.Word.ofNatModulo 22

def runOptions : SourceCoreExecution.RunOptions := {
  executionFuel := 100000
  inputValidationFuel := 1000
  outputValidationFuel := 1000 }

structure ObservedCall {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (flag : Bool) (value : Core.Word) where
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start observed.row.key [.bool flag, .word value] runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion artifact
  executed : session.RunAt observed.row.key [.bool flag, .word value] runOptions (.ok (.succeeded completion))
  returned : completion.value = .word value

def observeCall {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (flag : Bool) (value : Core.Word) : IO (ObservedCall observed session flag value) := do
  match started : session.start observed.row.key [.bool flag, .word value] runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint =>
    let executed ← session.runWithReceipt observed.row.key [.bool flag, .word value] runOptions
    match result : executed.val with
    | .error error => throw (IO.userError (reprStr error))
    | .ok (.failed _ _) => throw (IO.userError "named conditional failed")
    | .ok (.exportError error _) => throw (IO.userError (reprStr error))
    | .ok (.outOfFuel _) => throw (IO.userError "named conditional exhausted its execution budget")
    | .ok (.succeeded completion) =>
      if returned : completion.value = .word value then
        return ⟨checkpoint, started, completion, result ▸ executed.property, returned⟩
      else throw (IO.userError "named conditional returned an unexpected Word")

structure ObservedInitial (fixture : CompiledFixture) (observed : ObservedFactory fixture) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facadeCompiled
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  call : ObservedCall observed session true firstValue

def observeInitial (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ObservedInitial fixture observed) := do
  let opened ← fixture.facadeCompiled.openWithReceipt
  let fresh ← opened.val.bootstrapWithExportReceipt
  match ready : fresh.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "named conditional bootstrap exhausted")
  | .ready session =>
    let call ← observeCall observed session true firstValue
    return ⟨opened.val, opened.property, fresh.val, fresh.property.1, fresh.property.2, session, ready, call⟩

structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedFactory fixture) where
  initial : ObservedInitial fixture observed
  next : ObservedCall observed initial.call.completion.session false secondValue

def observeSequence (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ObservedSequence fixture observed) := do
  let initial ← observeInitial fixture observed
  let next ← observeCall observed initial.call.completion.session false secondValue
  return ⟨initial, next⟩

structure ObservedReceiver (fixture : CompiledFixture) (observed : ObservedFactory fixture) where
  completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics
  registry : completion.result.context.registry = fixture.recipe.compiled.compatible.checked.staticRegistry

theorem initial_receiver (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    Nonempty (ObservedReceiver fixture observed) := by
  obtain ⟨receiver, _entry, registry, issued⟩ :=
    CallableIndexedOwnedPublicFaultReceivers.Receiver.at_registry fixture.recipe.compiled observed.entry
      fixture.recipe.compiled.compatible.checked.staticRegistry (.refl _)
  exact ⟨⟨receiver, issued, registry⟩⟩

private theorem recipe_unique {compiled : SourceCoreExecution.Compiled}
    {first second : SourceCoreIndexedSession.Recipe}
    (left : RecursiveNamedPreparedStageContracts.PublicRecipe compiled first)
    (right : RecursiveNamedPreparedStageContracts.PublicRecipe compiled second) : first = second := by
  cases compiled
  exact Option.some.inj (left.symm.trans right)

theorem ObservedInitial.start_receipt {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (executed : ObservedInitial fixture observed) :
    ∃ (artifact : SourceCoreIndexedSession.Artifact)
      (session : SourceCoreIndexedSession.Session artifact)
      (checkpoint : SourceCoreIndexedSession.Checkpoint artifact)
      (root : SourceCoreIndexedSession.Root fixture.recipe.compiled)
      (world : Core.StoreTyping) (store : Core.Store) (native : Core.Environment)
      (encodedValues : SourceCoreCompatibleValues.Context),
      executed.artifact.IndexedAt fixture.facadeCompiled fixture.recipe artifact ∧
      SourceCoreIndexedSession.Recipe.prepare fixture.recipe.compiled = .ok fixture.recipe ∧
      executed.session.IndexedAt session ∧ executed.call.checkpoint.IndexedAt checkpoint ∧
      RecursiveNamedPublicStartMeaning.StartAt session observed.row.key [.bool true, .word firstValue]
        runOptions.inputValidationFuel checkpoint fixture.recipe root world store native encodedValues := by
  obtain ⟨recipe, artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, _program, sessionAt, checkpointAt, started⟩ :=
    RecursiveNamedPublicExecutionMeaning.actual_start fixture.accepted executed.opened executed.call.started
  have same := recipe_unique opened.compiled_recipe fixture.issued
  cases same
  exact ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
    opened, prepared, sessionAt, checkpointAt, started⟩

theorem ObservedInitial.metadata_at_start {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (executed : ObservedInitial fixture observed)
    {artifact : SourceCoreIndexedSession.Artifact} {session : SourceCoreIndexedSession.Session artifact}
    {checkpoint : SourceCoreIndexedSession.Checkpoint artifact}
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {world : Core.StoreTyping} {store : Core.Store} {native : Core.Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (opened : executed.artifact.IndexedAt fixture.facadeCompiled fixture.recipe artifact)
    (sessionAt : executed.session.IndexedAt session)
    (started : RecursiveNamedPublicStartMeaning.StartAt session observed.row.key [.bool true, .word firstValue]
      runOptions.inputValidationFuel checkpoint fixture.recipe root world store native encodedValues) :
    encodedValues.registry = fixture.recipe.compiled.compatible.checked.staticRegistry := by
  have ready : executed.bootstrap.ReadyAt 100000 executed.session := .single executed.ready
  obtain ⟨bootstrap, initialized, value, initialStore, _atBootstrap, initial, initializedAt, _done, booted⟩ :=
    ready.indexed opened executed.fresh
  have same : initialized = session := initializedAt.unique sessionAt
  subst initialized
  apply started.simple_registry (booted.registry_at initial)
  intro value member
  rcases List.mem_cons.mp member with same | member
  · exact same ▸ SourceCoreIndexedSession.SimplePublic.bool true
  · have same := List.mem_singleton.mp member
    exact same ▸ SourceCoreIndexedSession.SimplePublic.word firstValue

end Tests.SourceCoreNamedBranch
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedBranchSyntax
/-! The actual checked conditional supplies both lexical arms and the stopping
receipts for their dead suffix. All child certificates describe local reads. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreNamedBranch
open Solcore Frontend SourceInference SourceSemantics CoreLowering

private theorem form_typed {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {node : StatementNode} {facts : StatementFacts}
    (unique : NodeOccurrencesUnique source)
    (typed : StatementHasType source control context node.id final facts)
    (found : source.lookupStatement? node.id = some node) :
    Dynamic.StatementHasType.FormTyping source control context node.form final := by
  obtain ⟨actual, contains, form⟩ := Dynamic.StatementHasType.formTyping typed
  have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  subst actual
  exact form

private theorem returning {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {binder : TypedBinder}
    {statement : StatementNode} {facts : StatementFacts} {mode : Bool}
    (read : WordRead source binder) (unique : NodeOccurrencesUnique source)
    (typed : StatementHasType source control context statement.id final facts)
    (found : source.lookupStatement? statement.id = some statement)
    (form : statement.form = .returnStmt (some read.node.id))
    (type : statement.type = .word) (returns : control.returnType = .word) :
    GenericLexicalStatements.Syntax source (fun id => ∃ node name binderId,
      source.lookupExpression? id = some node ∧ node.form = .reference name (.local binderId))
      context mode [statement.id] .word := by
  have formTyped := form_typed unique typed found
  rw [form] at formTyped
  cases formTyped with
  | returnValue valueTyped =>
    exact .returnValue [] found form type read.found read.type
      (by simpa only [returns, read.type] using valueTyped) ⟨_, _, _, read.found, read.form⟩

theorem ActualHeader.branching_receipt {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt actual.header) := by
  apply CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.of_accepted actual.aligned.accepted _ actual.aligned.projection
  rw [actual.source, actual.statements]
  exact .conditional observed.shape.branchFound observed.shape.branchForm
    (.initialized observed.shape.initializedFound observed.shape.initializedForm
      (.returnValue [] observed.shape.thenReturnFound observed.shape.thenReturnForm))
    (.returnValue [] observed.shape.elseReturnFound observed.shape.elseReturnForm) .nil

def ActualHeader.branching_body {fixture : CompiledFixture} {row : SourceSpecialization.SpecializedFunction}
    (actual : ActualHeader fixture row)
    (receipt : CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt actual.header) :
    CallableIndexedOwnedPreparedStagedNamedBodies.Body actual.header := {
  row := row, prepared := actual.prepared, instantiation := CallableNamedMetadata.instantiation row
  aligned := actual.aligned, layouts := actual.aligned.layouts, compilation := .branching receipt }

theorem ActualHeader.syntax {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) :
    GenericLexicalStatements.Syntax actual.header.function.source (fun id => ∃ node name binderId,
      actual.header.function.source.lookupExpression? id = some node ∧ node.form = .reference name (.local binderId))
      actual.header.context true actual.header.function.body actual.header.function.resultType := by
  obtain ⟨facts, final, typed, _roots, _complete⟩ := actual.aligned.bodyTyped
  rw [actual.source, observed.shape.roots, actual.result_type] at typed
  simp only [List.filterMap_cons, List.filterMap_nil] at typed
  rw [actual.source, actual.statements, actual.result_type]
  have unique : NodeOccurrencesUnique observed.row.function.typedBody := actual.source ▸ actual.header.unique
  cases typed with
  | singleton head =>
    have formTyped := form_typed unique head observed.shape.branchFound
    rw [observed.shape.branchForm] at formTyped
    cases formTyped with
    | ifWithElse conditionTyped yes no =>
      cases yes with
      | cons initialized tail =>
        have initialTyped := form_typed unique initialized observed.shape.initializedFound
        rw [observed.shape.initializedForm] at initialTyped
        have thenStopped : GenericLexicalStatements.Stopped observed.row.function.typedBody
            [observed.shape.initialized.id, observed.shape.thenReturn.id] := GenericLexicalStatements.Stopped.of_source
          (ReachableStatementContinuations.StoppingStatements.prefix observed.shape.initializedFound initialized
            (.stop (.returnValue observed.shape.thenReturnFound observed.shape.thenReturnForm)))
        have elseStopped : GenericLexicalStatements.Stopped observed.row.function.typedBody
            [observed.shape.elseReturn.id] := GenericLexicalStatements.Stopped.of_source
          (ReachableStatementContinuations.StoppingStatements.stop
            (.returnValue observed.shape.elseReturnFound observed.shape.elseReturnForm))
        apply GenericLexicalStatements.Syntax.terminalIf unique observed.shape.branchFound observed.shape.branchForm
          observed.shape.branchType observed.shape.conditionRead.found observed.shape.conditionRead.type
          (by simpa only [observed.shape.conditionRead.type] using conditionTyped)
          ⟨_, _, _, observed.shape.conditionRead.found, observed.shape.conditionRead.form⟩
        · cases initialTyped with
          | letInitialized initializer mono extended =>
            apply GenericLexicalStatements.Syntax.initialized observed.shape.initializedFound observed.shape.initializedForm
              observed.local_declaration mono extended
              (by simp [observed.shape.inputs, Ne.symm observed.shape.localFlag, Ne.symm observed.shape.localArgument])
              observed.shape.initialRead.found
              (by simp [observed.shape.initialRead.type, observed.shape.localScheme, TypeSystem.Scheme.mono])
              (by simpa only [observed.shape.initialRead.type, observed.shape.localScheme, TypeSystem.Scheme.mono] using initializer)
              ⟨_, _, _, observed.shape.initialRead.found, observed.shape.initialRead.form⟩
            cases tail with
            | singleton last =>
              exact returning observed.shape.localRead unique last observed.shape.thenReturnFound
                observed.shape.thenReturnForm observed.shape.thenReturnType rfl
          | letInitializedGeneralized polymorphic _ _ _ _ =>
            exact False.elim (polymorphic (by simp [observed.shape.localScheme, TypeSystem.Scheme.mono]))
        · cases no with
          | singleton last =>
              exact returning observed.shape.elseRead unique last observed.shape.elseReturnFound
                observed.shape.elseReturnForm observed.shape.elseReturnType rfl
        · exact thenStopped
        · exact elseStopped

end Tests.SourceCoreNamedBranch
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedBranchSupports
/-! The complete authentic singleton catalog selects the named branching
compiler packet and derives all static children from actual local-read lowering. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreNamedBranch
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body)
open CallableIndexedOwnedPreparedStagedNamedBodiesSupport (Support)

structure StaticSupportPackage (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (registry : SourceCoreRawMetadata.Registry)
    (completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed) where
  input : Input fixture.recipe.compiled
  packet : Issued input
  actual : ActualHeader fixture observed.row
  headerEq : actual.header = packet.header
  rows : Inventory [input]
  rowsEq : rows = .cons packet .nil
  complete : RecursiveNamedCatalogNativeContexts.Complete
    (values := .initial fixture.recipe.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) (headers rows)
  terminals : ∀ header, header ∈ headers rows → Body header
  supports : ∀ header (member : header ∈ headers rows),
    Support (headers rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture))
      (terminals header member) (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
  family : ∀ {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association (headers rows)
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      mapping world function native bindings parameter result),
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor (actualStagePrepared fixture) association
  descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named actual.header.named.signature.key)

 theorem StaticSupportPackage.header_list {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {registry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (support : StaticSupportPackage fixture observed registry completion) : headers support.rows = [support.actual.header] := by
  rw [support.rowsEq, support.headerEq]
  rfl


theorem ActualHeader.support {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row)
    (receipt : CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt actual.header)
    (rootHeaders : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)))
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) rootHeaders)
    {registry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics) :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedBranchingSupport.Support rootHeaders
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry actual.header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) receipt
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  apply Nonempty.intro
  apply CallableIndexedOwnedPreparedNamedBranchingCollectors.of_compiler actual.prepared actual.aligned
    fixture.recipePrepared actual.diagnostic fixture.source_wellFormed complete (bootstrap_zero fixture.recipe.compiled)
    observed.entryMember receipt
    (CallableIndexedOwnedPreparedNamedBranchingCollectors.operands_of_diagnostic
      actual.prepared actual.aligned actual.diagnostic receiver)
    (CallableIndexedOwnedPreparedNamedBranchingCollectors.unary_of_diagnostic
      actual.prepared actual.aligned actual.diagnostic receiver) _ actual.syntax
  intro child selected context fields scope fuel id node lowered declarations approved found typed accepted nativeType _native
  obtain ⟨original, name, localId, lookup, form⟩ := approved
  have same := Option.some.inj (found.symm.trans lookup)
  subst original
  obtain ⟨root⟩ := CallableIndexedOwnedPreparedStagedNamedLexicalReadRoots.of_accepted
    actual.prepared actual.aligned actual.diagnostic receiver fixture.source_wellFormed
    (by rw [actual.source]; exact observed.metadata actual.prepared.named)
    ((RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected)
    ((RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).evidence selected) fields
    (by rw [(RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected]; exact declarations)
    (by rw [(RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected]; exact found)
    form
    (by rw [(RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected]; exact typed)
    (by rw [(RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected]; exact accepted)
  exact .recursive root

theorem static_supports (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed) (registry : SourceCoreRawMetadata.Registry)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics) :
    Nonempty (StaticSupportPackage fixture observed registry completion) := by
  obtain ⟨input, _row, packet, actual, sameHeader⟩ := stages.inventory
  let rows : Inventory [input] := .cons packet .nil
  have headerList : headers rows = [actual.header] := by simp only [rows, headers, sameHeader]
  have complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) (headers rows) := by
    rw [headerList]; exact actual.complete stages
  obtain ⟨receipt⟩ := actual.branching_receipt
  let body := actual.branching_body receipt
  obtain ⟨supported⟩ := actual.support receipt (headers rows) complete (registry := registry) receiver
  let terminals : ∀ header, header ∈ headers rows → Body header := fun header member => by
    have same : header = actual.header := by simpa only [headerList, List.mem_singleton] using member
    exact same ▸ body
  have supports : ∀ header (member : header ∈ headers rows),
      Support (headers rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        registry header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture))
        (terminals header member) (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
    intro header member
    have same : header = actual.header := by simpa only [headerList, List.mem_singleton] using member
    subst header
    simpa only [terminals, body, ActualHeader.branching_body, Support] using supported
  have family : ∀ {mapping world function native bindings parameter result}
      (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association (headers rows)
        (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) registry
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
        mapping world function native bindings parameter result),
      CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor (actualStagePrepared fixture) association := by
    intro mapping world function native bindings parameter result association
    cases association with
    | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
      have found := code.sourceFound
      rw [support.source.trans (stages.source_of_cached actual support.caller.selected)] at found
      exact False.elim (observed.no_lambda (lookupExpression?_sound found) code.sourceForm)
    | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
      exact False.elim (fixture.no_principal support.principal)
  exact ⟨{
    input := input
    packet := packet
    actual := actual
    headerEq := sameHeader
    rows := rows
    rowsEq := rfl
    complete := complete
    terminals := terminals
    supports := supports
    family := family
    descriptor := actual.descriptor stages }⟩

end Tests.SourceCoreNamedBranch
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedBranchCommon
/-! Retained callers connect the exact sessions and Source heaps of both named calls. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreNamedBranch
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open RecursiveNamedPublicFunctionHistory (Entry)

abbrev PublicSupports {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (receiver : ObservedReceiver fixture observed) :=
  StaticSupportPackage fixture observed receiver.completion.result.context.registry receiver.completion

def PublicSupports.functions {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :=
  CallableIndexedOwnedContextualCellOrigins.functions (headers support.rows)
    (keys fixture.recipe.compiled) receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics) observed.profile

theorem PublicSupports.observations {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :
    CompatibleEquality.FunctionObservations fixture.recipe.compiled.compatible.checked.catalog
      support.functions (CallableIndexedLambdaValues.Identity fixture.recipe.compiled.indexed) := by
  intro metadata mapping world sourceType source native type origin
  exact CallableIndexedOwnedGeneralLambdaValues.observations _ receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
    observed.profile (registry := metadata)
    (CallableIndexedOwnedContextualCellOrigins.functions_include_general observed.profile origin)

structure RetainedState {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {publicArtifact : SourceCoreExecution.Artifact} (publicSession : SourceCoreExecution.Session publicArtifact)
    (entries : List Entry) where
  artifact : SourceCoreIndexedSession.Artifact
  session : SourceCoreIndexedSession.Session artifact
  mapping : GeneralHeap.LocationMap
  world : Core.StoreTyping
  heap : Dynamic.Heap
  store : Core.Store
  caller : RecursiveNamedPublicFunctionHistory.Caller (headers support.rows)
    (keys fixture.recipe.compiled) mapping world heap store
  atSession : publicSession.IndexedAt session
  atRecipe : RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact fixture.recipe
  receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    receiving.entry receiving.result.context.registry receiving.result.extension receiving.result.diagnostics
  extension : SourceCoreRawMetadata.Extends receiver.completion.result.context.registry receiving.result.context.registry
  registry : session.RegistryAt receiving.result.context.registry
  history : RecursiveNamedPublicFunctionHistory.History (headers support.rows)
    (keys fixture.recipe.compiled) support.functions receiving.result.context.registry
    support.actual.header session mapping world heap store caller entries

def SourceCall {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (arguments : List Dynamic.Value)
    (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ rawD function size,
    CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD function ∧
    Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) size invocation
      support.actual.header.function.context before (.global function) arguments outcome after

end Tests.SourceCoreNamedBranch
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedBranchSeed
/-! The initial true-arm call derives its Source trace, Word result and reusable
empty history from actual bootstrap, input encoding and public completion. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNamedBranch
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

theorem first_meaning {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed}
    (support : PublicSupports receiver) (stages : ObservedStages fixture observed)
    (first : ObservedInitial fixture observed) :
    ∃ state : RetainedState support first.call.completion.session [],
      SourceCall support support.actual.header
        (RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function)
        ⟨[]⟩ [.bool true, .word firstValue] (.value (.word firstValue)) state.heap := by
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree fixture.recipe.compiled receiver.issued)
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ := first.start_receipt
  have startupRegistry := first.metadata_at_start opened sessionAt started
  obtain ⟨selectedHeader, selected⟩ := started.selection prepared support.complete
  have selectedEq : selectedHeader = support.actual.header := by
    have member := selected.member
    rw [support.header_list] at member
    exact List.mem_singleton.mp member
  subst selectedHeader
  have inputs : RecursiveNamedPublicNestedInputs.Inputs support.rows session support.actual.header.function.context
      (support.actual.header.bindings.map (fun binding => binding.1.scheme.body))
      [.bool true, .word firstValue] [.bool true, .word firstValue] := by
    rw [support.actual.input_types]
    exact .cons (.leaf (.data
      ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩
      ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩))
      (.cons (.leaf (.data
        ⟨.word firstValue, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word firstValue⟩
        ⟨.word firstValue, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word firstValue⟩)) .nil)
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiver.completion.result.context.registry := by
    rw [startupRegistry]
    exact receiver.completion.result.extension
  have sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt support.actual.header support.input.prepared.available
      (CallableNamedReversal.global (CallableNamedMetadata.global support.packet.header.named.specialized support.input.prepared.available)) := by
    rw [support.headerEq]
    exact support.packet.sourceAt
  obtain ⟨caller, actual, generation, value, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, result,
      returnedCaller, added, handles, _related, retained⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedHistoryPublicSeed.public_run_succeeded_collects
      (inputs := [support.input]) (rows := support.rows) (distinct := by simp)
      (stagePrepared := actualStagePrepared fixture) (receiver := receiver.issued)
      (profile := observed.profile) (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := support.terminals) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := prepared) (selected := selected)
      (opened := opened) (fresh := first.fresh) (ready := .single first.ready)
      (sameRuntime := SourceCoreExecution.Session.SameRuntime.refl first.session) (atSession := sessionAt)
      (atCheckpoint := checkpointAt) (started := started) (inputReceipts := inputs)
      (metadata := metadata) (sourceAt := sourceAt)
      (invocation := RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function)
      first.call.started first.call.executed .skip support.descriptor
  have empty : added = [] := List.map_eq_nil_iff.mp handles
  subst added
  have returnedRegistry := started.returned_registry succeeded
  rw [startupRegistry] at returnedRegistry
  have atRecipe : artifact.RecipeAt fixture.recipe := by
    cases artifact
    exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2
  rw [resultType, support.actual.result_type] at requested
  have outcomeValue := RecursiveNamedPublicWordResultMeaning.result_word succeeded requested
    (valueEq.symm.trans first.call.returned) support.actual.output result
  let state : RetainedState support first.call.completion.session [] := {
    artifact := artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := returnedCaller
    atSession := returnedAt
    atRecipe := started.recipe_eq
    receiving := receiver.completion
    issued := receiver.issued
    extension := .refl _
    registry := receiver.registry.symm ▸ returnedRegistry
    history := retained }
  exact ⟨state, support.input.prepared.available, _, sourceSize, sourceAt, outcomeValue ▸ trace⟩

end Tests.SourceCoreNamedBranch
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedBranchStep
/-! The false arm starts from the exact session and heap reached by the true arm. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNamedBranch
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

theorem RetainedState.choose {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (state : RetainedState support session []) {flag : Bool} {value : Core.Word}
    (call : ObservedCall observed session flag value) (invocation : Staging.Recursive.Scope) :
    ∃ after : RetainedState support call.completion.session [],
      SourceCall support support.actual.header invocation state.heap [.bool flag, .word value]
        (.value (.word value)) after.heap := by
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree fixture.recipe.compiled receiver.issued)
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.input] support.rows support.complete
    state.atRecipe state.history.current.1 state.atSession call.started
  have selectedHeader : request.header = support.actual.header := by
    have singleton : ∀ header, header ∈ headers support.rows → header = support.actual.header := by
      intro header member
      rw [support.header_list] at member
      exact List.mem_singleton.mp member
    exact singleton _ request.selected.member
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs [] request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [.bool flag, .word value] [.bool flag, .word value] := by
    rw [selectedHeader, support.actual.input_types]
    exact .cons (.data ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩
      ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩)
      (.cons (.data ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩
      ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩) .nil)
  have registry := request.started.simple_registry state.registry (by
    intro publicValue member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .bool flag
    · exact .word value)
  have metadata : SourceCoreRawMetadata.Extends request.encodedValues.registry state.receiving.result.context.registry := by
    rw [registry]; exact .refl _
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selectedHeader]; exact support.descriptor
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨actual, generation, native, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, result,
      reached, _related, retained⟩ :=
    CallableIndexedOwnedPreparedStagedHistoryPublicContinuations.public_run_succeeded_retains
      (inputs := [support.input]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture) (completion := state.receiving)
      (receiver := state.issued) (profile := observed.profile) (observations := support.observations)
      (extension := state.receiving.result.extension) (semantic := semantic)
      (family := support.family) (namedTerminals := support.terminals) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := fixture.recipePrepared)
      (selected := request.selected) (caller := state.caller) (history := state.history)
      (atCheckpoint := request.atCheckpoint) (started := request.started)
      (inputReceipts := inputs) (metadata := metadata) (sourceAt := request.sourceAt)
      (invocation := invocation) call.started call.executed descriptor
  have atRecipe : state.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType, selectedHeader, support.actual.result_type] at requested
  have outcomeValue := RecursiveNamedPublicWordResultMeaning.result_word succeeded requested
    (valueEq.symm.trans call.returned) (by rw [selectedHeader]; exact support.actual.output) result
  have returnedRegistry := request.started.returned_registry succeeded
  rw [registry] at returnedRegistry
  let next : RetainedState support call.completion.session [] := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := returnedAt
    atRecipe := state.atRecipe
    receiving := state.receiving
    issued := state.issued
    extension := state.extension
    registry := returnedRegistry
    history := retained }
  refine ⟨next, request.rawD, request.function, sourceSize, ?_, ?_⟩
  · rw [← selectedHeader]; exact request.sourceAt
  · simpa only [outcomeValue] using trace

end Tests.SourceCoreNamedBranch
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedBranchInitialForward
/-! The independent true-arm trace determines both public fuel bounds at its
original checkpoint. Every sufficient resume returns Word11 and the same heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNamedBranch
open Solcore Frontend SourceInference SourceSemantics CoreLowering

/-- The initial entry exports its genuine raw result type and returns the exact
Source heap in a reusable session at every sufficient pair of fuel budgets. -/
def InitialForwardAt {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (first : ObservedInitial fixture observed) (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome first.artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      first.call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion first.artifact,
        outcome = .succeeded completion ∧
        completion.value = .word firstValue ∧
        completion.session.ExportsReady ∧
        ∃ returned : RetainedState support completion.session [], returned.heap = after

theorem forward_initial {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (first : ObservedInitial fixture observed)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}
    (trace : SourceCall support support.actual.header invocation ⟨[]⟩ [.bool true, .word firstValue] (.value (.word firstValue)) after) :
    InitialForwardAt support first after := by
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree fixture.recipe.compiled receiver.issued)
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ := first.start_receipt
  obtain ⟨selectedHeader, selected⟩ := started.selection prepared support.complete
  have selectedEq : selectedHeader = support.actual.header := by
    have member := selected.member
    rw [support.header_list] at member
    exact List.mem_singleton.mp member
  subst selectedHeader
  have inputs : RecursiveNamedPublicNestedInputs.Inputs support.rows session support.actual.header.function.context
      (support.actual.header.bindings.map (fun binding => binding.1.scheme.body)) [.bool true, .word firstValue] [.bool true, .word firstValue] := by
    rw [support.actual.input_types]
    exact .cons (.leaf (.data
      ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩
      ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩))
      (.cons (.leaf (.data
      ⟨.word firstValue, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word firstValue⟩
      ⟨.word firstValue, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word firstValue⟩)) .nil)
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  obtain ⟨receiving, contextAt, issued, extended, _diagnostics, _caller, _capture,
      _payload, _finalStore, _finalMap, _finalWorld, requiredExecution, requiredOutput,
      _nativeEnough, _fullResult, publicEnough⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedOutputPreservation.public_resume_has_sufficient_fuel
      (inputs := [support.input]) (rows := support.rows) (distinct := by simp)
      (stagePrepared := actualStagePrepared fixture) (receiver := receiver.issued)
      (profile := observed.profile) (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (baseRegistry := receiver.registry)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := support.terminals)
      (namedSupport := support.supports) (wellFormed := fixture.source_wellFormed)
      (prepared := prepared) (selected := selected) (opened := opened)
      (fresh := first.fresh) (ready := .single first.ready) (authority := first.authority)
      (atSession := sessionAt) (atCheckpoint := checkpointAt) (started := started)
      (inputReceipts := inputs) (sourceAt := sourceAt) applied
  have atRecipe : artifact.RecipeAt fixture.recipe := by
    cases artifact
    exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  have rawResult := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2
  rw [rawResult, support.actual.result_type] at requested
  have nativeWord : _payload = .word firstValue := by
    have represented := _fullResult.2.1
    rw [support.actual.output] at represented
    cases represented with
    | value related =>
      obtain ⟨word, same, native⟩ := CompatibleExpressionPrimitives.word_fields related
      exact native.trans (congrArg Core.Value.word (Dynamic.Value.word.inj same).symm)
  refine ⟨requiredExecution, requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, _generation, reached, succeeded, exported, actualAt,
      _related, history, registry, ready⟩ :=
    publicEnough executionFuel outputFuel outcome executionBound outputBound resumed
  let returned : RetainedState support completion.session [] := {
    artifact := artifact
    session := actual.session
    mapping := _finalMap
    world := _finalWorld
    heap := after
    store := _finalStore
    caller := reached
    atSession := actualAt.2.2.2
    atRecipe := started.recipe_eq
    receiving := receiving
    issued := issued
    extension := extended
    registry := (congrArg (·.registry) contextAt).symm ▸ registry
    history := history }
  exact ⟨completion, succeeded, actualAt.1.trans ((nativeWord ▸ exported).word_value requested),
    actualAt.2.2.2.exportsReady_iff.mpr ready, returned, rfl⟩


end Tests.SourceCoreNamedBranch
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedBranchForward
/-! Following named execution derives sufficient public fuel from the independent
Source trace at the exact retained heap. The output and next history follow for
every sufficient resume of the original checkpoint. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNamedBranch
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

def ForwardAt {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {flag : Bool} {value : Core.Word} (call : ObservedCall observed session flag value)
    (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion artifact,
        outcome = .succeeded completion ∧ completion.value = .word value ∧
        completion.session.ExportsReady ∧
        ∃ returned : RetainedState support completion.session [], returned.heap = after

theorem forward_choose {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (state : RetainedState support session []) {flag : Bool} {value : Core.Word}
    (call : ObservedCall observed session flag value) (ready : session.ExportsReady)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}
    (trace : SourceCall support support.actual.header invocation state.heap
      [.bool flag, .word value] (.value (.word value)) after) :
    ForwardAt support call after := by
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree fixture.recipe.compiled receiver.issued)
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.input] support.rows support.complete
    state.atRecipe state.history.current.1 state.atSession call.started
  have selectedHeader : request.header = support.actual.header := by
    have singleton : ∀ header, header ∈ headers support.rows → header = support.actual.header := by
      intro header member
      rw [support.header_list] at member
      exact List.mem_singleton.mp member
    exact singleton _ request.selected.member
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs [] request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [.bool flag, .word value] [.bool flag, .word value] := by
    rw [selectedHeader, support.actual.input_types]
    exact .cons (.data ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩
      ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩)
      (.cons (.data ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩
      ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩) .nil)
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  have sourceAt' : CallableIndexedOwnedFunctionValues.NamedSourceAt request.header rawD function := by
    rw [selectedHeader]; exact sourceAt
  obtain ⟨receiving, contextAt, issued, extended, _diagnostics, _capture,
      payload, finalStore, finalMap, finalWorld, requiredExecution, requiredOutput,
      _nativeEnough, fullResult, publicEnough⟩ :=
    RecursiveNamedPublicActualRegistryNamedOutputPreservation.public_resume_has_sufficient_fuel
      (inputs := [support.input]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture) (completion := state.receiving)
      (receiver := state.issued) (profile := observed.profile) (observations := support.observations)
      (semantic := semantic) (family := support.family)
      (namedTerminals := support.terminals) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := fixture.recipePrepared)
      (selected := request.selected) (caller := state.caller) (history := state.history)
      (atCheckpoint := request.atCheckpoint) (started := request.started)
      (inputReceipts := inputs) (atRegistry := state.registry)
      (exportsReady := state.atSession.exportsReady_iff.mp ready) (sourceAt := sourceAt') applied
  have atRecipe : state.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType, selectedHeader, support.actual.result_type] at requested
  have nativeWord : payload = .word value := by
    have represented := fullResult.2.1
    rw [selectedHeader, support.actual.output] at represented
    cases represented with
    | value related =>
      obtain ⟨word, same, native⟩ := CompatibleExpressionPrimitives.word_fields related
      exact native.trans (congrArg Core.Value.word (Dynamic.Value.word.inj same).symm)
  refine ⟨requiredExecution, requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, _generation, reached, succeeded, exported, actualAt,
      _related, history, registry, returnedReady⟩ :=
    publicEnough executionFuel outputFuel outcome executionBound outputBound resumed
  let returned : RetainedState support completion.session [] := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := actualAt.2.2.2
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := state.extension.trans extended
    registry := (congrArg (·.registry) contextAt).symm ▸ registry
    history := history }
  exact ⟨completion, succeeded, actualAt.1.trans ((nativeWord ▸ exported).word_value requested),
    actualAt.2.2.2.exportsReady_iff.mpr returnedReady, returned, rfl⟩

end Tests.SourceCoreNamedBranch
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedBranchPublicExecution
/-! An independently checked and compiled named conditional exercises both
arms through the public API. Its real returned session carries the first
heap into the second call; each Source trace also entails sufficient public
execution and output fuel at that call's original checkpoint. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNamedBranch
open Solcore Frontend SourceInference SourceSemantics CoreLowering

theorem closed_sequence_meaning (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed) (sequence : ObservedSequence fixture observed) :
    ∃ (receiver : ObservedReceiver fixture observed) (support : PublicSupports receiver)
      (first : RetainedState support sequence.initial.call.completion.session [])
      (second : RetainedState support sequence.next.completion.session []),
      SourceCall support support.actual.header
        (RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function)
        ⟨[]⟩ [.bool true, .word firstValue] (.value (.word firstValue)) first.heap ∧
      SourceCall support support.actual.header
        (RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function)
        first.heap [.bool false, .word secondValue] (.value (.word secondValue)) second.heap ∧
      InitialForwardAt support sequence.initial first.heap ∧
      ForwardAt support sequence.next second.heap := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  obtain ⟨support⟩ := static_supports fixture observed stages receiver.completion.result.context.registry receiver.issued
  obtain ⟨first, initialTrace⟩ := first_meaning support stages sequence.initial
  obtain ⟨second, nextTrace⟩ := first.choose sequence.next
    (RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function)
  have initialReady : sequence.initial.session.ExportsReady :=
    (show sequence.initial.bootstrap.ReadyAt 100000 sequence.initial.session from .single sequence.initial.ready).exportsReady
      sequence.initial.authority
  have firstReady := sequence.initial.call.executed.exportsReady initialReady
  exact ⟨receiver, support, first, second, initialTrace, nextTrace,
    forward_initial support sequence.initial initialTrace,
    forward_choose first sequence.next firstReady nextTrace⟩

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeFactory fixture
  let stages ← observeStages fixture observed
  let sequence ← observeSequence fixture observed
  have _meaning := closed_sequence_meaning fixture observed stages sequence
  IO.println "Actual named conditional: true11 then false22, exact Source histories and sufficient public fuel for both calls proved"

end Tests.SourceCoreNamedBranch
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedMatchSource
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedMatchFixture
/-! Actual compilation, selected inventory and static match observations for
one named Word function with a pattern allocation, outer mutation and return. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreNamedMatch
open Solcore Frontend SourceInference SourceSemantics

private def observeFact (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

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
  let signature :: _ := checked.program.signatures.functions
    | throw (IO.userError "factory signature missing")
  let seeds := [SourceCompiler.Seed.declaration signature.id]
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

structure ObservedFactory (fixture : CompiledFixture) where
  row : SourceSpecialization.SpecializedFunction
  shape : FactoryShape row.function fixture.signature
  member : row ∈ fixture.recipe.compiled.validationPlan.specializations
  sourceOwner : row.function.typedBody.owner = fixture.signature.id
  parameters : row.parameterSubstitution = []
  closed : row.assumptions = []
  ordinary : row.function.returnComptime = false
  resultType : row.function.inferredBodyType = .word
  target : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
    (CallableNamedMetadata.instantiation row) = .ok row.key
  nodes : row.function.typedBody.nodes = shape.nodeList
  noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []
  profile : fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true
  entry : SourceCoreCallableIndexedPrograms.Entry fixture.recipe.compiled.indexed.layouts
  entryMember : entry ∈ fixture.recipe.compiled.indexed.entries

abbrev ObservedFactory.inputs {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.inputs
abbrev ObservedFactory.roots {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.roots
abbrev ObservedFactory.value {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.value
abbrev ObservedFactory.argument {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.argument
abbrev ObservedFactory.binderScheme {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.argumentScheme

private def observeTarget (fixture : CompiledFixture) (row : SourceSpecialization.SpecializedFunction) :
    IO (PLift (SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) = .ok row.key)) := do
  match accepted : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) with
  | .error error => throw (IO.userError (reprStr error))
  | .ok key =>
    let ⟨same⟩ ← observeFact (key = row.key) "captured factory exact key"
    return ⟨by rw [accepted, same]⟩

def observeFactory (fixture : CompiledFixture) : IO (ObservedFactory fixture) := do
  match rows : fixture.recipe.compiled.validationPlan.specializations with
  | [row] =>
    let shape ← observeShape row.function fixture.signature
    match entries : fixture.recipe.compiled.indexed.entries with
    | [entry] =>
      let ⟨sourceOwner⟩ ← observeFact (row.function.typedBody.owner = fixture.signature.id) "named match source owner"
      let ⟨parameters⟩ ← observeFact (row.parameterSubstitution = []) "named match substitution"
      let ⟨closed⟩ ← observeFact (row.assumptions = []) "named match assumptions"
      let ⟨resultType⟩ ← observeFact (row.function.inferredBodyType = .word) "named match result type"
      let ⟨ordinary⟩ ← observeFact (row.function.returnComptime = false) "named match ordinary result"
      let ⟨target⟩ ← observeTarget fixture row
      let ⟨nodes⟩ ← observeFact (row.function.typedBody.nodes = shape.nodeList) "named match nodes"
      let ⟨noLocals⟩ ← observeFact (fixture.recipe.compiled.indexed.base.locals.bindings = []) "named match local catalog"
      let ⟨profile⟩ ← observeFact (fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true) "named match profile"
      return {
        row, shape, sourceOwner, parameters, closed, ordinary, resultType, target, nodes, noLocals, profile, entry
        member := by rw [rows]; exact .head []
        entryMember := by rw [entries]; exact .head [] }
    | _ => throw (IO.userError "named match entry count")
  | _ => throw (IO.userError "named match specialization count")

/-- The staged selection is obtained from the retained callable table and
original sidecar of the concrete compiler result. -/
structure ObservedStages (fixture : CompiledFixture)
    (observed : ObservedFactory fixture) where
  singletonGlobal : fixture.recipe.compiled.indexed.base.globals.length = 1
  descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named observed.row.key)
  native : SourceCoreGeneralFunctions.CallableContext
  present : fixture.recipe.compiled.indexed.base.callableContext = some native
  sidecar : SourceCoreStageContracts.Sidecar
  issued : SourceCoreStageContracts.prepareSidecar
    fixture.recipe.compiled.indexed.base.plan observed.row.key = .ok sidecar

def observeStages (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ObservedStages fixture observed) := do
  match present : fixture.recipe.compiled.indexed.base.callableContext with
  | none => throw (IO.userError "factory callable context missing")
  | some native =>
    match issued : SourceCoreStageContracts.prepareSidecar
        fixture.recipe.compiled.indexed.base.plan observed.row.key with
    | .error _ => throw (IO.userError "factory original sidecar missing")
    | .ok sidecar =>
      if singletonGlobal : fixture.recipe.compiled.indexed.base.globals.length = 1 then
        match SourceCoreCallableContracts.descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
            (.named observed.row.key) with
        | .error error => throw (IO.userError (reprStr error))
        | .ok descriptor => return ⟨singletonGlobal, descriptor, native, present, sidecar, issued⟩
      else throw (IO.userError "factory global count")

def ObservedStages.registry {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (_actual : ObservedStages fixture observed) : Staging.Recursive.Registry :=
  RecursiveNamedPreparedStageScopes.registry
    (RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected)

theorem ObservedStages.selected {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    stages.registry.Closure actual.header.function
      (RecursiveStageRegistry.scope stages.sidecar [] actual.header.function) := by
  have same := RecursiveNamedPreparedStageScopes.sidecar_caller stages.issued
    (CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.record actual.prepared actual.aligned)
  rw [actual.aligned.function]
  exact RecursiveNamedPreparedStageScopes.Selected.named actual.prepared stages.sidecar stages.issued same


theorem ActualHeader.complete {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [actual.header] := by
  have selected := CallableIndexedPreparedInventories.cached_global_at fixture.recipe.compiled actual.prepared.selected
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  rw [stages.singletonGlobal] at bound
  have zero : actual.prepared.index = 0 := by omega
  intro index signature found
  have bound := (List.getElem?_eq_some_iff.mp found).1
  rw [stages.singletonGlobal] at bound
  have indexZero : index = 0 := by omega
  refine ⟨actual.header, .head [], actual.aligned.slot.trans (zero.trans indexZero.symm), ?_⟩
  rw [actual.aligned.named]
  rw [zero] at selected
  rw [indexZero] at found
  exact Option.some.inj (selected.symm.trans found)

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


theorem ObservedStages.inventory {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) :
    ∃ input : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled,
      input.row = observed.row ∧
      ∃ packet : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued input,
      ∃ actual : ActualHeader fixture observed.row, actual.header = packet.header := by
  obtain ⟨prepared⟩ := fixture.prepared observed.member
  have range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures fixture.recipe.compiled.sourceProgram.signatures) observed.row.parameterSubstitution := by
    simp only [observed.parameters, SourceSemantics.ParameterSubstitution.RangeWellFormed,
      List.not_mem_nil, false_implies, implies_true]
  have metadata : CallableNamedCanonicalOrder.retainedInstantiation observed.row =
      CallableNamedMetadata.instantiation observed.row := by
    simp [CallableNamedCanonicalOrder.retainedInstantiation, CallableNamedMetadata.instantiation, observed.parameters]
  have target : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedCanonicalOrder.retainedInstantiation observed.row) = .ok prepared.named.signature.key := by
    rw [metadata, RecursiveNamedPreparedCallEvidence.Prepared.signature_key prepared]
    exact observed.target
  have selected := CallableIndexedPreparedInventories.cached_global_at fixture.recipe.compiled prepared.selected
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  rw [stages.singletonGlobal] at bound
  have zero : prepared.index = 0 := by omega
  have globals : fixture.recipe.compiled.indexed.base.globals = [prepared.named.signature] := by
    obtain ⟨first, single⟩ := List.length_eq_one_iff.mp stages.singletonGlobal
    rw [single, zero] at selected
    have same : first = prepared.named.signature := by simpa only [List.getElem?_cons_zero, Option.some.injEq] using selected
    exact single.trans (congrArg (fun value => [value]) same)
  let input : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled := {
    row := observed.row
    prepared := prepared
    range := range
    ordinaryReturn := observed.ordinary
    ordinaryParameters := by
      intro binder member
      rw [observed.inputs] at member
      rcases List.mem_cons.mp member with same | rest
      · exact same ▸ observed.shape.valueOrdinary
      · have same := List.mem_singleton.mp rest
        exact same ▸ observed.shape.argumentOrdinary
    target := target
    slot := by simp only [CallableNamedMetadata.Slot, globals, zero]; simp }
  obtain ⟨packet⟩ := CallableIndexedOwnedPreparedFiniteNamedInventories.issue fixture.source_wellFormed input
  let actual : ActualHeader fixture observed.row := {
    prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued prepared packet.selected
    header := packet.header
    aligned := by simpa only [input, metadata] using packet.aligned
    diagnostic := ⟨⟨packet.selected.diagnostics, packet.selected.found, rfl⟩⟩ }
  exact ⟨input, rfl, packet, actual, rfl⟩



theorem ObservedStages.source_of_cached {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : fixture.recipe.compiled.indexed.base.functions[index]? = some named) :
    CallableIndexedNamedGeneration.source named = observed.row.function.typedBody := by
  have length : fixture.recipe.compiled.indexed.base.functions.length = 1 := by
    simpa only [CallableIndexedPreparedInventories.cached_globals, List.length_map] using stages.singletonGlobal
  have before := (List.getElem?_eq_some_iff.mp actual.prepared.selected).1
  have after := (List.getElem?_eq_some_iff.mp selected).1
  rw [length] at before after
  have same : index = actual.prepared.index := by omega
  rw [same, actual.prepared.selected] at selected
  cases Option.some.inj selected
  exact congrArg (fun row => row.function.typedBody) actual.prepared.same

theorem CompiledFixture.no_principal (fixture : CompiledFixture)
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal fixture.recipe.compiled method) : False := by
  obtain ⟨_implementation, _method, _trait, _definition, _substitution, instantiated⟩ := principal.source_instantiation
  cases instantiated with
  | intro _ _ _ _ member _ _ _ _ _ _ _ =>
    simp only [Program.ofChecked, fixture.sameProgram, fixture.methods, List.map_nil,
      List.not_mem_nil] at member

theorem CompiledFixture.signature_member (fixture : CompiledFixture) :
    fixture.signature ∈ fixture.recipe.compiled.sourceProgram.signatures.functions := by
  rw [fixture.sameProgram, fixture.signatures]
  exact .head []

theorem ActualHeader.source {fixture : CompiledFixture} {row : SourceSpecialization.SpecializedFunction}
    (actual : ActualHeader fixture row) : actual.header.function.source = row.function.typedBody := by
  rw [actual.aligned.function]
  exact congrArg (fun row => row.function.typedBody) actual.prepared.same


theorem ActualHeader.body {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) : actual.header.function.body = observed.shape.body := by
  rw [actual.aligned.function]
  change actual.prepared.compilation.statements = [observed.shape.matchNode.id, observed.shape.statement.id]
  have accepted := actual.prepared.compilation.roots
  change (actual.prepared.named.specialized.function.typedBody.roots.mapM _) = _ at accepted
  rw [actual.prepared.same, observed.roots] at accepted
  exact (Except.ok.inj accepted).symm

theorem actualStagePrepared (fixture : CompiledFixture) :
    RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable :=
  RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
    fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected

end Tests.SourceCoreNamedMatch
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedMatchFacts
/-! Finite observations identify all original reads and exclude anonymous code.
They establish compiler coverage without an execution or body-meaning premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreNamedMatch
open Solcore Frontend SourceInference SourceSemantics CoreLowering

theorem ActualHeader.input_types {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.word, .word] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.shape.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    observed.shape.valueScheme, observed.shape.argumentScheme, TypeSystem.Scheme.mono] using inputs.symm

theorem ActualHeader.result_type {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) : actual.header.function.resultType = .word := by
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same]
  exact observed.resultType

theorem ActualHeader.output {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) : actual.header.output = .word := by
  have projected := actual.aligned.projection
  rw [actual.result_type] at projected
  exact (Except.ok.inj projected).symm

def ActualHeader.descriptor {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named actual.header.named.signature.key) := by
  rw [actual.aligned.named, RecursiveNamedPreparedCallEvidence.Prepared.signature_key actual.prepared]
  exact stages.descriptor

theorem ObservedFactory.read_cases {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {id : ExpressionId} {node : ExpressionNode}
    (found : ContainsExpression observed.row.function.typedBody id node) :
    node = observed.shape.initialRead.node ∨ node = observed.shape.localRead.node ∨ node = observed.shape.finalRead.node := by
  have member := found.1
  rw [observed.nodes] at member
  simpa only [FactoryShape.nodeList, List.mem_cons, List.mem_singleton, Node.expression.injEq,
    reduceCtorEq, List.not_mem_nil, false_or, or_false] using member

theorem ObservedFactory.metadata {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    (named : CallableIndexedNamedGeneration.Named) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.MetadataFor
      fixture.recipe.compiled.indexed named observed.row.function.typedBody := by
  apply CallableIndexedOwnedPreparedStagedReadLambdaMetadata.metadata _ named _ observed.noLocals
  intro id node found
  rcases observed.read_cases (lookupExpression?_sound found) with same | same | same
  all_goals subst node
  · exact .inl ⟨_, _, observed.shape.initialRead.form, observed.shape.initialRead.requirements, observed.shape.initialRead.coercions⟩
  · exact .inl ⟨_, _, observed.shape.localRead.form, observed.shape.localRead.requirements, observed.shape.localRead.coercions⟩
  · exact .inl ⟨_, _, observed.shape.finalRead.form, observed.shape.finalRead.requirements, observed.shape.finalRead.coercions⟩

theorem ObservedFactory.no_lambda {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {id : ExpressionId} {node : ExpressionNode}
    (found : ContainsExpression observed.row.function.typedBody id node)
    {parameters result body} (form : node.form = .lambda parameters result body) : False := by
  rcases observed.read_cases found with same | same | same
  all_goals subst node
  · rw [observed.shape.initialRead.form] at form; cases form
  · rw [observed.shape.localRead.form] at form; cases form
  · rw [observed.shape.finalRead.form] at form; cases form

theorem ObservedFactory.value_declaration {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    SourceCoreDataPlaces.rootBinder observed.row.function.typedBody observed.shape.value.id = .ok observed.shape.value := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, observed.inputs,
    observed.nodes, FactoryShape.nodeList, observed.shape.initialRead.form,
    observed.shape.localRead.form, observed.shape.finalRead.form, observed.shape.assignmentForm,
    observed.shape.matchForm, observed.shape.statementForm, observed.shape.arms, observed.shape.patternResolution, SourceCoreDataPlaces.patternBinders, observed.shape.valueOwner,
    observed.shape.valueScheme, TypeSystem.Scheme.mono, observed.shape.argumentValue,
    observed.shape.localValue, observed.shape.valueRequirements]

theorem ObservedFactory.local_declaration {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    SourceCoreDataPlaces.rootBinder observed.row.function.typedBody observed.shape.copyBinder.id = .ok observed.shape.copyBinder := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, observed.inputs,
    observed.nodes, FactoryShape.nodeList, observed.shape.initialRead.form,
    observed.shape.localRead.form, observed.shape.finalRead.form, observed.shape.assignmentForm,
    observed.shape.matchForm, observed.shape.statementForm, observed.shape.arms, observed.shape.patternResolution, SourceCoreDataPlaces.patternBinders,
    observed.shape.localOwner, observed.shape.localScheme, TypeSystem.Scheme.mono,
    observed.shape.localRequirements,
    Ne.symm observed.shape.localArgument, Ne.symm observed.shape.localValue]

theorem ActualHeader.statements {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) :
    actual.header.function.body = [observed.shape.matchNode.id, observed.shape.statement.id] := actual.body

end Tests.SourceCoreNamedMatch
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedMatchRuntime
/-! Actual public calls allocate a pattern-bound copy and update the outer parameter.
The second call consumes the exact session returned by the first. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreNamedMatch
open Solcore Frontend SourceInference SourceSemantics CoreLowering

def firstInput : Core.Word := Core.Word.ofNatModulo 11
def firstValue : Core.Word := Core.Word.ofNatModulo 12
def secondInput : Core.Word := Core.Word.ofNatModulo 22
def secondValue : Core.Word := Core.Word.ofNatModulo 23

def runOptions : SourceCoreExecution.RunOptions := {
  executionFuel := 100000
  inputValidationFuel := 1000
  outputValidationFuel := 1000 }

structure ObservedCall {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (previous : Core.Word) (value : Core.Word) where
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start observed.row.key [.word previous, .word value] runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion artifact
  executed : session.RunAt observed.row.key [.word previous, .word value] runOptions (.ok (.succeeded completion))
  returned : completion.value = .word value

def observeCall {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (previous : Core.Word) (value : Core.Word) : IO (ObservedCall observed session previous value) := do
  match started : session.start observed.row.key [.word previous, .word value] runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint =>
    let executed ← session.runWithReceipt observed.row.key [.word previous, .word value] runOptions
    match result : executed.val with
    | .error error => throw (IO.userError (reprStr error))
    | .ok (.failed _ _) => throw (IO.userError "named match failed")
    | .ok (.exportError error _) => throw (IO.userError (reprStr error))
    | .ok (.outOfFuel _) => throw (IO.userError "named match exhausted its execution budget")
    | .ok (.succeeded completion) =>
      if returned : completion.value = .word value then
        return ⟨checkpoint, started, completion, result ▸ executed.property, returned⟩
      else throw (IO.userError "named match returned an unexpected Word")

structure ObservedInitial (fixture : CompiledFixture) (observed : ObservedFactory fixture) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facadeCompiled
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  call : ObservedCall observed session firstInput firstValue

def observeInitial (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ObservedInitial fixture observed) := do
  let opened ← fixture.facadeCompiled.openWithReceipt
  let fresh ← opened.val.bootstrapWithExportReceipt
  match ready : fresh.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "named match bootstrap exhausted")
  | .ready session =>
    let call ← observeCall observed session firstInput firstValue
    return ⟨opened.val, opened.property, fresh.val, fresh.property.1, fresh.property.2, session, ready, call⟩

structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedFactory fixture) where
  initial : ObservedInitial fixture observed
  next : ObservedCall observed initial.call.completion.session secondInput secondValue

def observeSequence (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ObservedSequence fixture observed) := do
  let initial ← observeInitial fixture observed
  let next ← observeCall observed initial.call.completion.session secondInput secondValue
  return ⟨initial, next⟩

structure ObservedReceiver (fixture : CompiledFixture) (observed : ObservedFactory fixture) where
  completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics
  registry : completion.result.context.registry = fixture.recipe.compiled.compatible.checked.staticRegistry

theorem initial_receiver (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    Nonempty (ObservedReceiver fixture observed) := by
  obtain ⟨receiver, _entry, registry, issued⟩ :=
    CallableIndexedOwnedPublicFaultReceivers.Receiver.at_registry fixture.recipe.compiled observed.entry
      fixture.recipe.compiled.compatible.checked.staticRegistry (.refl _)
  exact ⟨⟨receiver, issued, registry⟩⟩

private theorem recipe_unique {compiled : SourceCoreExecution.Compiled}
    {first second : SourceCoreIndexedSession.Recipe}
    (left : RecursiveNamedPreparedStageContracts.PublicRecipe compiled first)
    (right : RecursiveNamedPreparedStageContracts.PublicRecipe compiled second) : first = second := by
  cases compiled
  exact Option.some.inj (left.symm.trans right)

theorem ObservedInitial.start_receipt {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (executed : ObservedInitial fixture observed) :
    ∃ (artifact : SourceCoreIndexedSession.Artifact)
      (session : SourceCoreIndexedSession.Session artifact)
      (checkpoint : SourceCoreIndexedSession.Checkpoint artifact)
      (root : SourceCoreIndexedSession.Root fixture.recipe.compiled)
      (world : Core.StoreTyping) (store : Core.Store) (native : Core.Environment)
      (encodedValues : SourceCoreCompatibleValues.Context),
      executed.artifact.IndexedAt fixture.facadeCompiled fixture.recipe artifact ∧
      SourceCoreIndexedSession.Recipe.prepare fixture.recipe.compiled = .ok fixture.recipe ∧
      executed.session.IndexedAt session ∧ executed.call.checkpoint.IndexedAt checkpoint ∧
      RecursiveNamedPublicStartMeaning.StartAt session observed.row.key [.word firstInput, .word firstValue]
        runOptions.inputValidationFuel checkpoint fixture.recipe root world store native encodedValues := by
  obtain ⟨recipe, artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, _program, sessionAt, checkpointAt, started⟩ :=
    RecursiveNamedPublicExecutionMeaning.actual_start fixture.accepted executed.opened executed.call.started
  have same := recipe_unique opened.compiled_recipe fixture.issued
  cases same
  exact ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
    opened, prepared, sessionAt, checkpointAt, started⟩

theorem ObservedInitial.metadata_at_start {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (executed : ObservedInitial fixture observed)
    {artifact : SourceCoreIndexedSession.Artifact} {session : SourceCoreIndexedSession.Session artifact}
    {checkpoint : SourceCoreIndexedSession.Checkpoint artifact}
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {world : Core.StoreTyping} {store : Core.Store} {native : Core.Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (opened : executed.artifact.IndexedAt fixture.facadeCompiled fixture.recipe artifact)
    (sessionAt : executed.session.IndexedAt session)
    (started : RecursiveNamedPublicStartMeaning.StartAt session observed.row.key [.word firstInput, .word firstValue]
      runOptions.inputValidationFuel checkpoint fixture.recipe root world store native encodedValues) :
    encodedValues.registry = fixture.recipe.compiled.compatible.checked.staticRegistry := by
  have ready : executed.bootstrap.ReadyAt 100000 executed.session := .single executed.ready
  obtain ⟨bootstrap, initialized, value, initialStore, _atBootstrap, initial, initializedAt, _done, booted⟩ :=
    ready.indexed opened executed.fresh
  have same : initialized = session := initializedAt.unique sessionAt
  subst initialized
  apply started.simple_registry (booted.registry_at initial)
  intro value member
  rcases List.mem_cons.mp member with same | member
  · exact same ▸ SourceCoreIndexedSession.SimplePublic.word firstInput
  · have same := List.mem_singleton.mp member
    exact same ▸ SourceCoreIndexedSession.SimplePublic.word firstValue

end Tests.SourceCoreNamedMatch
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedMatchSyntax
/-! Original typing supplies the match's pattern local, assignment and
outer return to the actual compiler's static syntax certificate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNamedMatch
open Solcore Frontend SourceInference SourceSemantics CoreLowering

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
  have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  subst actual
  exact original

private theorem returning {source : TypedSource} {context final : SourceSemantics.Context}
    {binder : TypedBinder} {id : StatementId} {node : StatementNode} {facts : StatementFacts}
    {approved : ExpressionId → Prop} {mode : Bool} {rest : List StatementId}
    (unique : NodeOccurrencesUnique source) (read : Read source binder .word)
    (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt (some read.node.id))
    (annotation : node.type = .word) (leaf : approved read.node.id)
    (typed : StatementHasType source {returnType := .word} context id final facts) :
    GenericImperativeMatch.Syntax source approved context (.statements mode (id :: rest)) .word := by
  have original := form_at unique found typed
  rw [form] at original
  cases original with
  | returnValue value =>
      exact .body (.returnValue rest found form annotation read.found read.type
        (by simpa only [read.type] using value) leaf)

private theorem assigned {source : TypedSource} {context : SourceSemantics.Context}
    {binder rhsBinder : TypedBinder} {payload : TypeSystem.Ty} {id : StatementId} {node : StatementNode}
    {assignment : AssignmentResolution} {approved : ExpressionId → Prop} {mode : Bool} {rest : List StatementId}
    (read : Read source rhsBinder payload) (found : source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment .equal read.node.id)
    (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
    (scheme : binder.scheme = .mono payload) (bare : assignment.target.projections = [])
    (targetType : assignment.target.type = payload) (leaf : approved read.node.id)
    (typed : SourceAssignmentHasType source context assignment .equal read.node.id)
    (remaining : GenericImperativeMatch.Syntax source approved context (.statements mode rest) .word) :
    GenericImperativeMatch.Syntax source approved context (.statements mode (id :: rest)) .word := by
  cases typed with
  | wordCompound operator _ _ _ => cases operator
  | equal target rhs _requirements =>
      cases target with
      | intro writable projections target =>
          apply GenericImperativeMatch.Syntax.assign found form
          · intro actual actualFound
            have same := Except.ok.inj (declaration.symm.trans actualFound)
            subst actual
            rw [scheme, bare, targetType]
            exact .nil _
          · intro actual actualFound
            have same := Except.ok.inj (declaration.symm.trans actualFound)
            subst actual
            rw [bare] at projections
            cases projections
            have word := target.symm.trans targetType
            simpa only [word, scheme, TypeSystem.Scheme.mono] using writable
          · simpa only [target] using rhs
          · exact .inl rfl
          · intro child member
            simp only [bare, DataPlaceKeyOrder.sourceKeys, List.mem_cons, List.not_mem_nil, or_false] at member
            subst child
            exact ⟨leaf, read.node, read.found, by simpa only [← target, targetType, read.type] using rhs⟩
          · exact remaining

theorem ObservedFactory.body_shape {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    CallableIndexedOwnedPreparedStagedBranchingTree.Shape observed.row.function.typedBody true observed.shape.body := by
  apply CallableIndexedOwnedPreparedStagedBranchingTree.Shape.matchWith observed.shape.matchFound observed.shape.matchForm
  · intro arm member
    have same : arm = observed.shape.arm := by simpa only [observed.shape.arms, List.mem_singleton] using member
    subst arm
    rw [observed.shape.armBody]
    exact .assign observed.shape.assignmentFound observed.shape.assignmentForm (.inl rfl) observed.shape.targetBare .nil
  · intro statements present
    simp [observed.shape.noDefault] at present
  · exact .returnValue [] observed.shape.statementFound observed.shape.statementForm

private theorem binders_functional {owner : Resolved.DeclarationId}
    {context left right : SourceSemantics.Context} {binders : List TypedBinder}
    (first : BindersExtend owner context binders left) (second : BindersExtend owner context binders right) : left = right := by
  induction first generalizing right with
  | nil => cases second; rfl
  | cons head tail ih =>
    cases second with
    | cons other rest => cases head; cases other; exact ih rest

private theorem requested_body {source : TypedSource} {control : ControlContext}
    {parent child : SourceSemantics.Context} {type : TypeSystem.Ty} {cases : List TypedMatchCase}
    {caseFacts : List BodyFacts} {fallback : Option (List StatementId)} {request : GenericMatchChildren.Request}
    (typed : MatchCasesHaveType source control parent type cases caseFacts)
    (defaultTyped : ∀ statements, fallback = some statements →
      ∃ final facts, StatementsHaveType source control parent statements final facts)
    (selected : GenericMatchChildren.ContextFor source parent type cases fallback request child) :
    ∃ final facts, StatementsHaveType source control child request.statements final facts := by
  cases selected with
  | @arm arm binders arity child member statements patternTyped extended =>
    have caseTyped : ∃ facts, MatchCaseHasType source control parent type arm facts := by
      induction cases generalizing caseFacts with
      | nil => cases member
      | cons head rest ih =>
        cases typed with
        | cons headTyped tail =>
          rcases List.mem_cons.mp member with same | later
          · subst arm; exact ⟨_, headTyped⟩
          · exact ih tail later
    obtain ⟨facts, caseTyped⟩ := caseTyped
    cases caseTyped with
    | intro originalPattern originalExtension body =>
      have bindersEq := (CompatiblePatternSourceBinders.pattern_binders originalPattern).symm.trans
        (CompatiblePatternSourceBinders.pattern_binders patternTyped)
      cases bindersEq
      have same := binders_functional originalExtension extended
      rw [← same, statements]
      exact ⟨_, _, body⟩
  | default present => exact defaultTyped _ present

def ObservedFactory.readIds {fixture : CompiledFixture} (observed : ObservedFactory fixture) : List ExpressionId :=
  [observed.shape.initialRead.node.id, observed.shape.localRead.node.id, observed.shape.finalRead.node.id]

theorem ObservedFactory.body_syntax {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (unique : NodeOccurrencesUnique observed.row.function.typedBody) {approved : ExpressionId → Prop}
    (leaves : ∀ id ∈ observed.readIds, approved id)
    (typed : StatementsHaveType observed.row.function.typedBody {returnType := .word}
      context observed.shape.body final facts) :
    GenericImperativeMatch.Syntax observed.row.function.typedBody approved context
      (.statements true observed.shape.body) .word := by
  have leaf : ∀ id, id ∈ observed.readIds → approved id := leaves
  obtain ⟨middle, headFacts, tailFacts, first, tail⟩ := head_tail typed
  have firstForm := form_at unique observed.shape.matchFound first
  rw [observed.shape.matchForm] at firstForm
  cases firstForm with
  | matchWithDefault present _ _ _ => simp [observed.shape.noDefault] at present
  | matchWithoutDefault absent scrutineeTyped casesTyped =>
    have scrutineeFound : observed.row.function.typedBody.lookupExpression? observed.shape.matching.scrutinee =
        some observed.shape.initialRead.node := by rw [observed.shape.scrutinee]; exact observed.shape.initialRead.found
    obtain ⟨stored, contained, storedType⟩ := scrutineeTyped.stored_type
    have same := Option.some.inj ((lookupExpression?_complete unique contained).symm.trans scrutineeFound)
    subst stored
    have defaults : ∀ statements, observed.shape.matching.defaultBody = some statements →
        ∃ final facts, StatementsHaveType observed.row.function.typedBody {returnType := .word} context statements final facts := by
      intro statements present; simp [observed.shape.noDefault] at present
    apply GenericImperativeMatch.Syntax.matchWith observed.shape.matchFound observed.shape.matchForm
      (.inl observed.shape.matchType) scrutineeFound (storedType ▸ scrutineeTyped)
      (by rw [observed.shape.scrutinee]; exact leaf _ (by simp [readIds]))
      (storedType ▸ casesTyped) defaults
    · simp [observed.shape.inputs, Ne.symm observed.shape.hiddenValue, Ne.symm observed.shape.hiddenArgument]
    · intro arm member binder binderMember
      have same : arm = observed.shape.arm := by simpa only [observed.shape.arms, List.mem_singleton] using member
      subst arm
      have sameBinder : binder = observed.shape.copyBinder.id := by
        simpa [TypedMatchPattern.binderIds, observed.shape.patternResolution] using binderMember
      subst binder
      simp [observed.shape.inputs, Ne.symm observed.shape.localValue, Ne.symm observed.shape.localArgument]
    · intro request child selected
      have original := requested_body (storedType ▸ casesTyped) defaults selected
      have statements : request.statements = [observed.shape.assignment.id] := by
        cases selected with
        | @arm arm _ _ _ member sameBody _ _ =>
          have same : arm = observed.shape.arm := by simpa only [observed.shape.arms, List.mem_singleton] using member
          subst arm
          exact sameBody.trans observed.shape.armBody
        | default present => simp [observed.shape.noDefault] at present
      rw [statements]
      obtain ⟨final, bodyFacts, bodyTyped⟩ := original
      rw [statements] at bodyTyped
      obtain ⟨_, _, _, assignedHead, _⟩ := head_tail bodyTyped
      have assignment := form_at unique observed.shape.assignmentFound assignedHead
      rw [observed.shape.assignmentForm] at assignment
      cases assignment with
      | assignValue assignmentTyped =>
        exact assigned observed.shape.localRead observed.shape.assignmentFound observed.shape.assignmentForm
          (by rw [observed.shape.targetRoot]; exact observed.value_declaration)
          observed.shape.valueScheme observed.shape.targetBare observed.shape.targetType
          (leaf _ (by simp [readIds])) assignmentTyped (.body (.nil (.inl rfl)))
    · obtain ⟨_, _, _, returningHead, _⟩ := head_tail tail
      exact returning unique observed.shape.finalRead observed.shape.statementFound observed.shape.statementForm
        observed.shape.statementType (leaf _ (by simp [readIds])) returningHead

theorem ActualHeader.syntax {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) :
    GenericImperativeMatch.Syntax actual.header.function.source (fun id => ∃ node name binderId,
      actual.header.function.source.lookupExpression? id = some node ∧ node.form = .reference name (.local binderId))
      actual.header.context (.statements true actual.header.function.body) actual.header.function.resultType := by
  obtain ⟨facts, final, typed, _roots, _complete⟩ := actual.aligned.bodyTyped
  rw [actual.source, observed.shape.roots, actual.result_type] at typed
  simp only [List.filterMap_cons, List.filterMap_nil] at typed
  rw [actual.source, actual.body, actual.result_type]
  apply observed.body_syntax (actual.source ▸ actual.header.unique) _ typed
  intro id member
  simp only [ObservedFactory.readIds, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact ⟨_, _, _, observed.shape.initialRead.found, observed.shape.initialRead.form⟩
  · exact ⟨_, _, _, observed.shape.localRead.found, observed.shape.localRead.form⟩
  · exact ⟨_, _, _, observed.shape.finalRead.found, observed.shape.finalRead.form⟩

theorem ActualHeader.branching_receipt {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt actual.header) := by
  apply CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.of_accepted actual.aligned.accepted _ actual.aligned.projection
  rw [actual.source, actual.body]
  exact observed.body_shape

def ActualHeader.branching_body {fixture : CompiledFixture} {row : SourceSpecialization.SpecializedFunction}
    (actual : ActualHeader fixture row)
    (receipt : CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt actual.header) :
    CallableIndexedOwnedPreparedStagedNamedBodies.Body actual.header := {
  row := row, prepared := actual.prepared, instantiation := CallableNamedMetadata.instantiation row
  aligned := actual.aligned, layouts := actual.aligned.layouts, compilation := .branching receipt }

end Tests.SourceCoreNamedMatch
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedMatchSupports
/-! The complete authentic singleton catalog selects the named branching
compiler packet and derives all static children from actual local-read lowering. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreNamedMatch
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body)
open CallableIndexedOwnedPreparedStagedNamedBodiesSupport (Support)

structure StaticSupportPackage (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (registry : SourceCoreRawMetadata.Registry)
    (completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed) where
  input : Input fixture.recipe.compiled
  packet : Issued input
  actual : ActualHeader fixture observed.row
  headerEq : actual.header = packet.header
  rows : Inventory [input]
  rowsEq : rows = .cons packet .nil
  complete : RecursiveNamedCatalogNativeContexts.Complete
    (values := .initial fixture.recipe.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) (headers rows)
  terminals : ∀ header, header ∈ headers rows → Body header
  supports : ∀ header (member : header ∈ headers rows),
    Support (headers rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture))
      (terminals header member) (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
  family : ∀ {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association (headers rows)
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      mapping world function native bindings parameter result),
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor (actualStagePrepared fixture) association
  descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named actual.header.named.signature.key)

 theorem StaticSupportPackage.header_list {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {registry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (support : StaticSupportPackage fixture observed registry completion) : headers support.rows = [support.actual.header] := by
  rw [support.rowsEq, support.headerEq]
  rfl


theorem ActualHeader.support {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row)
    (receipt : CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt actual.header)
    (rootHeaders : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)))
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) rootHeaders)
    {registry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics) :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedBranchingSupport.Support rootHeaders
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry actual.header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) receipt
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  apply Nonempty.intro
  apply CallableIndexedOwnedPreparedNamedBranchingCollectors.of_imperative_compiler actual.prepared actual.aligned
    fixture.recipePrepared actual.diagnostic fixture.source_wellFormed complete (bootstrap_zero fixture.recipe.compiled)
    observed.entryMember receipt
    (CallableIndexedOwnedPreparedNamedBranchingCollectors.operands_of_diagnostic
      actual.prepared actual.aligned actual.diagnostic receiver)
    (CallableIndexedOwnedPreparedNamedBranchingCollectors.unary_of_diagnostic
      actual.prepared actual.aligned actual.diagnostic receiver) _ actual.syntax.prepared
  intro child selected context fields scope fuel id node lowered declarations approved found typed accepted nativeType _native
  obtain ⟨original, name, localId, lookup, form⟩ := approved
  have same := Option.some.inj (found.symm.trans lookup)
  subst original
  obtain ⟨root⟩ := CallableIndexedOwnedPreparedStagedNamedLexicalReadRoots.of_accepted
    actual.prepared actual.aligned actual.diagnostic receiver fixture.source_wellFormed
    (by rw [actual.source]; exact observed.metadata actual.prepared.named)
    ((RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected)
    ((RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).evidence selected) fields
    (by rw [(RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected]; exact declarations)
    (by rw [(RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected]; exact found)
    form
    (by rw [(RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected]; exact typed)
    (by rw [(RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected]; exact accepted)
  exact .recursive root

theorem static_supports (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed) (registry : SourceCoreRawMetadata.Registry)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics) :
    Nonempty (StaticSupportPackage fixture observed registry completion) := by
  obtain ⟨input, _row, packet, actual, sameHeader⟩ := stages.inventory
  let rows : Inventory [input] := .cons packet .nil
  have headerList : headers rows = [actual.header] := by simp only [rows, headers, sameHeader]
  have complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) (headers rows) := by
    rw [headerList]; exact actual.complete stages
  obtain ⟨receipt⟩ := actual.branching_receipt
  let body := actual.branching_body receipt
  obtain ⟨supported⟩ := actual.support receipt (headers rows) complete (registry := registry) receiver
  let terminals : ∀ header, header ∈ headers rows → Body header := fun header member => by
    have same : header = actual.header := by simpa only [headerList, List.mem_singleton] using member
    exact same ▸ body
  have supports : ∀ header (member : header ∈ headers rows),
      Support (headers rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        registry header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture))
        (terminals header member) (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
    intro header member
    have same : header = actual.header := by simpa only [headerList, List.mem_singleton] using member
    subst header
    simpa only [terminals, body, ActualHeader.branching_body, Support] using supported
  have family : ∀ {mapping world function native bindings parameter result}
      (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association (headers rows)
        (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) registry
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
        mapping world function native bindings parameter result),
      CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor (actualStagePrepared fixture) association := by
    intro mapping world function native bindings parameter result association
    cases association with
    | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
      have found := code.sourceFound
      rw [support.source.trans (stages.source_of_cached actual support.caller.selected)] at found
      exact False.elim (observed.no_lambda (lookupExpression?_sound found) code.sourceForm)
    | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
      exact False.elim (fixture.no_principal support.principal)
  exact ⟨{
    input := input
    packet := packet
    actual := actual
    headerEq := sameHeader
    rows := rows
    rowsEq := rfl
    complete := complete
    terminals := terminals
    supports := supports
    family := family
    descriptor := actual.descriptor stages }⟩

end Tests.SourceCoreNamedMatch
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedMatchCommon
/-! Retained callers connect the exact sessions and Source heaps of both named calls. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreNamedMatch
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open RecursiveNamedPublicFunctionHistory (Entry)

abbrev PublicSupports {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (receiver : ObservedReceiver fixture observed) :=
  StaticSupportPackage fixture observed receiver.completion.result.context.registry receiver.completion

def PublicSupports.functions {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :=
  CallableIndexedOwnedContextualCellOrigins.functions (headers support.rows)
    (keys fixture.recipe.compiled) receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics) observed.profile

theorem PublicSupports.observations {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :
    CompatibleEquality.FunctionObservations fixture.recipe.compiled.compatible.checked.catalog
      support.functions (CallableIndexedLambdaValues.Identity fixture.recipe.compiled.indexed) := by
  intro metadata mapping world sourceType source native type origin
  exact CallableIndexedOwnedGeneralLambdaValues.observations _ receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
    observed.profile (registry := metadata)
    (CallableIndexedOwnedContextualCellOrigins.functions_include_general observed.profile origin)

structure RetainedState {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {publicArtifact : SourceCoreExecution.Artifact} (publicSession : SourceCoreExecution.Session publicArtifact)
    (entries : List Entry) where
  artifact : SourceCoreIndexedSession.Artifact
  session : SourceCoreIndexedSession.Session artifact
  mapping : GeneralHeap.LocationMap
  world : Core.StoreTyping
  heap : Dynamic.Heap
  store : Core.Store
  caller : RecursiveNamedPublicFunctionHistory.Caller (headers support.rows)
    (keys fixture.recipe.compiled) mapping world heap store
  atSession : publicSession.IndexedAt session
  atRecipe : RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact fixture.recipe
  receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    receiving.entry receiving.result.context.registry receiving.result.extension receiving.result.diagnostics
  extension : SourceCoreRawMetadata.Extends receiver.completion.result.context.registry receiving.result.context.registry
  registry : session.RegistryAt receiving.result.context.registry
  history : RecursiveNamedPublicFunctionHistory.History (headers support.rows)
    (keys fixture.recipe.compiled) support.functions receiving.result.context.registry
    support.actual.header session mapping world heap store caller entries

def SourceCall {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (arguments : List Dynamic.Value)
    (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ rawD function size,
    CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD function ∧
    Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) size invocation
      support.actual.header.function.context before (.global function) arguments outcome after

end Tests.SourceCoreNamedMatch
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedMatchSeed
/-! The initial match call derives its Source trace, Word result and reusable
empty history from actual bootstrap, input encoding and public completion. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNamedMatch
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

theorem first_meaning {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed}
    (support : PublicSupports receiver) (stages : ObservedStages fixture observed)
    (first : ObservedInitial fixture observed) :
    ∃ state : RetainedState support first.call.completion.session [],
      SourceCall support support.actual.header
        (RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function)
        ⟨[]⟩ [.word firstInput, .word firstValue] (.value (.word firstValue)) state.heap := by
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree fixture.recipe.compiled receiver.issued)
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ := first.start_receipt
  have startupRegistry := first.metadata_at_start opened sessionAt started
  obtain ⟨selectedHeader, selected⟩ := started.selection prepared support.complete
  have selectedEq : selectedHeader = support.actual.header := by
    have member := selected.member
    rw [support.header_list] at member
    exact List.mem_singleton.mp member
  subst selectedHeader
  have inputs : RecursiveNamedPublicNestedInputs.Inputs support.rows session support.actual.header.function.context
      (support.actual.header.bindings.map (fun binding => binding.1.scheme.body))
      [.word firstInput, .word firstValue] [.word firstInput, .word firstValue] := by
    rw [support.actual.input_types]
    exact .cons (.leaf (.data
      ⟨.word firstInput, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word firstInput⟩
      ⟨.word firstInput, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word firstInput⟩))
      (.cons (.leaf (.data
        ⟨.word firstValue, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word firstValue⟩
        ⟨.word firstValue, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word firstValue⟩)) .nil)
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiver.completion.result.context.registry := by
    rw [startupRegistry]
    exact receiver.completion.result.extension
  have sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt support.actual.header support.input.prepared.available
      (CallableNamedReversal.global (CallableNamedMetadata.global support.packet.header.named.specialized support.input.prepared.available)) := by
    rw [support.headerEq]
    exact support.packet.sourceAt
  obtain ⟨caller, actual, generation, value, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, result,
      returnedCaller, added, handles, _related, retained⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedHistoryPublicSeed.public_run_succeeded_collects
      (inputs := [support.input]) (rows := support.rows) (distinct := by simp)
      (stagePrepared := actualStagePrepared fixture) (receiver := receiver.issued)
      (profile := observed.profile) (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := support.terminals) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := prepared) (selected := selected)
      (opened := opened) (fresh := first.fresh) (ready := .single first.ready)
      (sameRuntime := SourceCoreExecution.Session.SameRuntime.refl first.session) (atSession := sessionAt)
      (atCheckpoint := checkpointAt) (started := started) (inputReceipts := inputs)
      (metadata := metadata) (sourceAt := sourceAt)
      (invocation := RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function)
      first.call.started first.call.executed .skip support.descriptor
  have empty : added = [] := List.map_eq_nil_iff.mp handles
  subst added
  have returnedRegistry := started.returned_registry succeeded
  rw [startupRegistry] at returnedRegistry
  have atRecipe : artifact.RecipeAt fixture.recipe := by
    cases artifact
    exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2
  rw [resultType, support.actual.result_type] at requested
  have outcomeValue := RecursiveNamedPublicWordResultMeaning.result_word succeeded requested
    (valueEq.symm.trans first.call.returned) support.actual.output result
  let state : RetainedState support first.call.completion.session [] := {
    artifact := artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := returnedCaller
    atSession := returnedAt
    atRecipe := started.recipe_eq
    receiving := receiver.completion
    issued := receiver.issued
    extension := .refl _
    registry := receiver.registry.symm ▸ returnedRegistry
    history := retained }
  exact ⟨state, support.input.prepared.available, _, sourceSize, sourceAt, outcomeValue ▸ trace⟩

end Tests.SourceCoreNamedMatch
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedMatchStep
/-! The following match call starts from the exact session and heap reached by the first call. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNamedMatch
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

theorem RetainedState.update {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (state : RetainedState support session []) {previous : Core.Word} {value : Core.Word}
    (call : ObservedCall observed session previous value) (invocation : Staging.Recursive.Scope) :
    ∃ after : RetainedState support call.completion.session [],
      SourceCall support support.actual.header invocation state.heap [.word previous, .word value]
        (.value (.word value)) after.heap := by
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree fixture.recipe.compiled receiver.issued)
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.input] support.rows support.complete
    state.atRecipe state.history.current.1 state.atSession call.started
  have selectedHeader : request.header = support.actual.header := by
    have singleton : ∀ header, header ∈ headers support.rows → header = support.actual.header := by
      intro header member
      rw [support.header_list] at member
      exact List.mem_singleton.mp member
    exact singleton _ request.selected.member
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs [] request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [.word previous, .word value] [.word previous, .word value] := by
    rw [selectedHeader, support.actual.input_types]
    exact .cons (.data ⟨.word previous, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word previous⟩
      ⟨.word previous, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word previous⟩)
      (.cons (.data ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩
        ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩) .nil)
  have registry := request.started.simple_registry state.registry (by
    intro publicValue member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .word previous
    · exact .word value)
  have metadata : SourceCoreRawMetadata.Extends request.encodedValues.registry state.receiving.result.context.registry := by
    rw [registry]; exact .refl _
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selectedHeader]; exact support.descriptor
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨actual, generation, native, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, result,
      reached, _related, retained⟩ :=
    CallableIndexedOwnedPreparedStagedHistoryPublicContinuations.public_run_succeeded_retains
      (inputs := [support.input]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture) (completion := state.receiving)
      (receiver := state.issued) (profile := observed.profile) (observations := support.observations)
      (extension := state.receiving.result.extension) (semantic := semantic)
      (family := support.family) (namedTerminals := support.terminals) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := fixture.recipePrepared)
      (selected := request.selected) (caller := state.caller) (history := state.history)
      (atCheckpoint := request.atCheckpoint) (started := request.started)
      (inputReceipts := inputs) (metadata := metadata) (sourceAt := request.sourceAt)
      (invocation := invocation) call.started call.executed descriptor
  have atRecipe : state.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType, selectedHeader, support.actual.result_type] at requested
  have outcomeValue := RecursiveNamedPublicWordResultMeaning.result_word succeeded requested
    (valueEq.symm.trans call.returned) (by rw [selectedHeader]; exact support.actual.output) result
  have returnedRegistry := request.started.returned_registry succeeded
  rw [registry] at returnedRegistry
  let next : RetainedState support call.completion.session [] := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := returnedAt
    atRecipe := state.atRecipe
    receiving := state.receiving
    issued := state.issued
    extension := state.extension
    registry := returnedRegistry
    history := retained }
  refine ⟨next, request.rawD, request.function, sourceSize, ?_, ?_⟩
  · rw [← selectedHeader]; exact request.sourceAt
  · simpa only [outcomeValue] using trace

end Tests.SourceCoreNamedMatch
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedMatchInitialForward
/-! The independent nonempty-loop trace determines both public fuel bounds at its
original checkpoint. Every sufficient resume returns Word11 and the same heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNamedMatch
open Solcore Frontend SourceInference SourceSemantics CoreLowering

/-- The initial entry exports its genuine raw result type and returns the exact
Source heap in a reusable session at every sufficient pair of fuel budgets. -/
def InitialForwardAt {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (first : ObservedInitial fixture observed) (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome first.artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      first.call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion first.artifact,
        outcome = .succeeded completion ∧
        completion.value = .word firstValue ∧
        completion.session.ExportsReady ∧
        ∃ returned : RetainedState support completion.session [], returned.heap = after

theorem forward_initial {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (first : ObservedInitial fixture observed)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}
    (trace : SourceCall support support.actual.header invocation ⟨[]⟩ [.word firstInput, .word firstValue] (.value (.word firstValue)) after) :
    InitialForwardAt support first after := by
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree fixture.recipe.compiled receiver.issued)
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ := first.start_receipt
  obtain ⟨selectedHeader, selected⟩ := started.selection prepared support.complete
  have selectedEq : selectedHeader = support.actual.header := by
    have member := selected.member
    rw [support.header_list] at member
    exact List.mem_singleton.mp member
  subst selectedHeader
  have inputs : RecursiveNamedPublicNestedInputs.Inputs support.rows session support.actual.header.function.context
      (support.actual.header.bindings.map (fun binding => binding.1.scheme.body)) [.word firstInput, .word firstValue] [.word firstInput, .word firstValue] := by
    rw [support.actual.input_types]
    exact .cons (.leaf (.data
      ⟨.word firstInput, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word firstInput⟩
      ⟨.word firstInput, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word firstInput⟩))
      (.cons (.leaf (.data
        ⟨.word firstValue, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word firstValue⟩
        ⟨.word firstValue, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word firstValue⟩)) .nil)
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  obtain ⟨receiving, contextAt, issued, extended, _diagnostics, _caller, _capture,
      _payload, _finalStore, _finalMap, _finalWorld, requiredExecution, requiredOutput,
      _nativeEnough, _fullResult, publicEnough⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedOutputPreservation.public_resume_has_sufficient_fuel
      (inputs := [support.input]) (rows := support.rows) (distinct := by simp)
      (stagePrepared := actualStagePrepared fixture) (receiver := receiver.issued)
      (profile := observed.profile) (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (baseRegistry := receiver.registry)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := support.terminals)
      (namedSupport := support.supports) (wellFormed := fixture.source_wellFormed)
      (prepared := prepared) (selected := selected) (opened := opened)
      (fresh := first.fresh) (ready := .single first.ready) (authority := first.authority)
      (atSession := sessionAt) (atCheckpoint := checkpointAt) (started := started)
      (inputReceipts := inputs) (sourceAt := sourceAt) applied
  have atRecipe : artifact.RecipeAt fixture.recipe := by
    cases artifact
    exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  have rawResult := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2
  rw [rawResult, support.actual.result_type] at requested
  have nativeWord : _payload = .word firstValue := by
    have represented := _fullResult.2.1
    rw [support.actual.output] at represented
    cases represented with
    | value related =>
      obtain ⟨word, same, native⟩ := CompatibleExpressionPrimitives.word_fields related
      exact native.trans (congrArg Core.Value.word (Dynamic.Value.word.inj same).symm)
  refine ⟨requiredExecution, requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, _generation, reached, succeeded, exported, actualAt,
      _related, history, registry, ready⟩ :=
    publicEnough executionFuel outputFuel outcome executionBound outputBound resumed
  let returned : RetainedState support completion.session [] := {
    artifact := artifact
    session := actual.session
    mapping := _finalMap
    world := _finalWorld
    heap := after
    store := _finalStore
    caller := reached
    atSession := actualAt.2.2.2
    atRecipe := started.recipe_eq
    receiving := receiving
    issued := issued
    extension := extended
    registry := (congrArg (·.registry) contextAt).symm ▸ registry
    history := history }
  exact ⟨completion, succeeded, actualAt.1.trans ((nativeWord ▸ exported).word_value requested),
    actualAt.2.2.2.exportsReady_iff.mpr ready, returned, rfl⟩


end Tests.SourceCoreNamedMatch
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedMatchForward
/-! Following named execution derives sufficient public fuel from the independent
Source trace at the exact retained heap. The output and next history follow for
every sufficient resume of the original checkpoint. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNamedMatch
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

def ForwardAt {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {previous : Core.Word} {value : Core.Word} (call : ObservedCall observed session previous value)
    (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion artifact,
        outcome = .succeeded completion ∧ completion.value = .word value ∧
        completion.session.ExportsReady ∧
        ∃ returned : RetainedState support completion.session [], returned.heap = after

theorem forward_update {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (state : RetainedState support session []) {previous : Core.Word} {value : Core.Word}
    (call : ObservedCall observed session previous value) (ready : session.ExportsReady)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}
    (trace : SourceCall support support.actual.header invocation state.heap
      [.word previous, .word value] (.value (.word value)) after) :
    ForwardAt support call after := by
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree fixture.recipe.compiled receiver.issued)
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.input] support.rows support.complete
    state.atRecipe state.history.current.1 state.atSession call.started
  have selectedHeader : request.header = support.actual.header := by
    have singleton : ∀ header, header ∈ headers support.rows → header = support.actual.header := by
      intro header member
      rw [support.header_list] at member
      exact List.mem_singleton.mp member
    exact singleton _ request.selected.member
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs [] request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [.word previous, .word value] [.word previous, .word value] := by
    rw [selectedHeader, support.actual.input_types]
    exact .cons (.data ⟨.word previous, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word previous⟩
      ⟨.word previous, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word previous⟩)
      (.cons (.data ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩
        ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩) .nil)
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  have sourceAt' : CallableIndexedOwnedFunctionValues.NamedSourceAt request.header rawD function := by
    rw [selectedHeader]; exact sourceAt
  obtain ⟨receiving, contextAt, issued, extended, _diagnostics, _capture,
      payload, finalStore, finalMap, finalWorld, requiredExecution, requiredOutput,
      _nativeEnough, fullResult, publicEnough⟩ :=
    RecursiveNamedPublicActualRegistryNamedOutputPreservation.public_resume_has_sufficient_fuel
      (inputs := [support.input]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture) (completion := state.receiving)
      (receiver := state.issued) (profile := observed.profile) (observations := support.observations)
      (semantic := semantic) (family := support.family)
      (namedTerminals := support.terminals) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := fixture.recipePrepared)
      (selected := request.selected) (caller := state.caller) (history := state.history)
      (atCheckpoint := request.atCheckpoint) (started := request.started)
      (inputReceipts := inputs) (atRegistry := state.registry)
      (exportsReady := state.atSession.exportsReady_iff.mp ready) (sourceAt := sourceAt') applied
  have atRecipe : state.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType, selectedHeader, support.actual.result_type] at requested
  have nativeWord : payload = .word value := by
    have represented := fullResult.2.1
    rw [selectedHeader, support.actual.output] at represented
    cases represented with
    | value related =>
      obtain ⟨word, same, native⟩ := CompatibleExpressionPrimitives.word_fields related
      exact native.trans (congrArg Core.Value.word (Dynamic.Value.word.inj same).symm)
  refine ⟨requiredExecution, requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, _generation, reached, succeeded, exported, actualAt,
      _related, history, registry, returnedReady⟩ :=
    publicEnough executionFuel outputFuel outcome executionBound outputBound resumed
  let returned : RetainedState support completion.session [] := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := actualAt.2.2.2
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := state.extension.trans extended
    registry := (congrArg (·.registry) contextAt).symm ▸ registry
    history := history }
  exact ⟨completion, succeeded, actualAt.1.trans ((nativeWord ▸ exported).word_value requested),
    actualAt.2.2.2.exportsReady_iff.mpr returnedReady, returned, rfl⟩

end Tests.SourceCoreNamedMatch
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedMatchPublicExecution
/-! An independently checked and compiled named match allocates a pattern variable and
mutates an outer parameter through two public calls. Its real returned session carries the first
heap into the second call; each Source trace also entails sufficient public
execution and output fuel at that call's original checkpoint. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNamedMatch
open Solcore Frontend SourceInference SourceSemantics CoreLowering

theorem closed_sequence_meaning (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed) (sequence : ObservedSequence fixture observed) :
    ∃ (receiver : ObservedReceiver fixture observed) (support : PublicSupports receiver)
      (first : RetainedState support sequence.initial.call.completion.session [])
      (second : RetainedState support sequence.next.completion.session []),
      SourceCall support support.actual.header
        (RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function)
        ⟨[]⟩ [.word firstInput, .word firstValue] (.value (.word firstValue)) first.heap ∧
      SourceCall support support.actual.header
        (RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function)
        first.heap [.word secondInput, .word secondValue] (.value (.word secondValue)) second.heap ∧
      InitialForwardAt support sequence.initial first.heap ∧
      ForwardAt support sequence.next second.heap := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  obtain ⟨support⟩ := static_supports fixture observed stages receiver.completion.result.context.registry receiver.issued
  obtain ⟨first, initialTrace⟩ := first_meaning support stages sequence.initial
  obtain ⟨second, nextTrace⟩ := first.update sequence.next
    (RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function)
  have initialReady : sequence.initial.session.ExportsReady :=
    (show sequence.initial.bootstrap.ReadyAt 100000 sequence.initial.session from .single sequence.initial.ready).exportsReady
      sequence.initial.authority
  have firstReady := sequence.initial.call.executed.exportsReady initialReady
  exact ⟨receiver, support, first, second, initialTrace, nextTrace,
    forward_initial support sequence.initial initialTrace,
    forward_update first sequence.next firstReady nextTrace⟩

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeFactory fixture
  let stages ← observeStages fixture observed
  let sequence ← observeSequence fixture observed
  have _meaning := closed_sequence_meaning fixture observed stages sequence
  IO.println "Actual named match: (11,12)->12 then (22,23)->23, exact Source histories and sufficient public fuel for both calls proved"

end Tests.SourceCoreNamedMatch
end
