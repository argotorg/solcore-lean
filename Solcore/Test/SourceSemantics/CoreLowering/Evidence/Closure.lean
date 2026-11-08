import Solcore.Test.Frontend.Source.CompilerFeatureSupport
import Solcore.Test.SourceSemantics.CoreLowering.Evidence.Direct
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicInputRegistries
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalNamedCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.Bootstrap
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.CallRejection
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.SelectedGeneralCalls
import Solcore.SourceSemantics.SourceProgramCheckingSoundness
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedCanonicalSupport
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MethodSelection
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedEvidenceRoots
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicActualRegistry
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericImperativeMatchMeaning
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.BranchingTrees
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.LambdaBodySupport
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.OrdinaryMethodRoots
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MixedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.OrdinarySequenceCallers
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.InitializedPublicBounds

/-!
# Closure evidence tests

Evidence-passing closures through their family and public execution.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreEvidence
/-! Closed evidence and retained coercions run through ordinary cached Core
functions. The checker keeps its existing admission rules. -/
set_option autoImplicit false

namespace Tests.SourceCoreEvidence
open Solcore Solcore.Frontend SourceCoreExecution

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def w (value : Nat) : Core.Word := Core.Word.ofNatModulo value

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [],
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Marker<T> {}", "impl Marker<Word> {}",
    "function keep<T>(value: T) returns (T) where T: Marker { return value; }",
    "function relay<T>(value: T) returns (T) where T: Marker { return keep(value); }",
    "function constrained(value: Word) returns (Word) where Word: Marker { let table: mapping(Word => Word); table[0] = relay(value); return table[0]; }",
    "trait Coerce<From, To> { function coerce(value: From) returns (To); }",
    "impl Coerce<Bool, Word> { function coerce(value: Bool) returns (Word) { let table: mapping(Word => Word); table[0] = value ? 40 : 6; table[0] += 2; return table[0]; } }",
    "function converted(flag: Bool) returns (Word) { let table: mapping(Word => Word); table[0] = flag; return table[0]; }",
    "function indirect(flag: Bool) returns (Word) { let f: function(Word) returns (Word) = lam(value: Word) -> Word { return value + 5; }; return f(flag); }",
    "function identity(value: Word) returns (Word) { return value; }",
    "type WordFunction = function(Word) returns (Word);",
    "impl Coerce<Word, WordFunction> { function coerce(value: Word) returns (WordFunction) { return identity; } }",
    "function convertedFunction(value: Word) returns (WordFunction) { return value; }",
    "function useFunction(f: WordFunction, value: Word) returns (Word) { return f(value); }",
    "enum Token { A, B, C }",
    "trait Add<T> { function add(left: T, right: T) returns (T) where T: Marker; }",
    "trait BitNot<T> { function bnot(value: T) returns (T) where T: Marker; }",
    "impl Marker<Token> {}",
    "impl Add<Token> { function add(left: Token, right: Token) returns (Token) where Token: Marker { match (left) { case .A { return right; } case .B { return .C; } default { return .A; } } } }",
    "impl BitNot<Token> { function bnot(value: Token) returns (Token) where Token: Marker { match (value) { case .A { return .B; } case .B { return .C; } default { return .A; } } } }",
    "function operatorResult() returns (Token) { return ~(Token.A + Token.B); }",
    "function operatorEffects() returns (Word) { let count: Word = 0; let left = lam() -> Token { count = count * 10 + 1; return .A; }; let right = lam() -> Token { count = count * 10 + 2; return .B; }; let token: Token = left() + right(); return count; }"
  ]}]
}

private def compile (program : CheckedProgram) (name : String) : IO SourceCompilerFeatureSupport.Entry :=
  SourceCompilerFeatureSupport.compileNamed program name []
    {specializationBudget := 256, compilationFuel := 1000}

private def testWord (program : CheckedProgram) (name : String) (arguments : List Value)
    (expected : Nat) : IO Unit := do
  let compiled ← compile program name
  for _ in [0, 1] do
    assertTrue ((← compiled.run arguments) == .word (w expected)) s!"{name} Core evidence result changed"
  compiled.checkResume arguments (.word (w expected)) 0

def run : IO Unit := do
  let program ← match checkProgram workspace 4096 with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"evidence source rejected: {reprStr error}")
  testWord program "constrained" [.word (w 7)] 7
  for (flag, expected) in [(true, 42), (false, 8)] do
    testWord program "converted" [.bool flag] expected
    testWord program "indirect" [.bool flag] (expected + 5)
  -- Both operand closures assign only their call's copy of `count`.
  testWord program "operatorEffects" [] 0
  let token ← match program.signatures.dataTypes.filter (·.name == "Token") with
    | [token] => pure token
    | _ => throw (IO.userError "Token missing")
  let tokenType := TypeSystem.Ty.nominal token.id []
  let expected : Value := .constructed ⟨⟨token.id, 2⟩, [], [], tokenType⟩ []
  let compiled ← compile program "operatorResult"
  assertTrue ((← compiled.run []) == expected) "evidence-selected nominal operators changed"
  compiled.checkResume [] expected 0
  let seeds ← ["convertedFunction", "useFunction"].mapM fun name => do
    match program.signatures.functions.filter (·.name == name) with
    | [signature] => pure (SourceCoreCompiler.Seed.declaration signature.id)
    | _ => throw (IO.userError "function coercion root missing")
  let shared ← match SourceCoreExecution.compileChecked program seeds {compilationFuel := 256, specializationBudget := 256} with
    | .ok shared => pure shared
    | .error error => throw (IO.userError s!"function coercion session failed: {reprStr error}")
  let artifact ← shared.open
  let session ← SourceCompilerFeatureSupport.boot artifact
  let producer ← match shared.keys[0]? with | some key => pure key | none => throw (IO.userError "producer missing")
  let consumer ← match shared.keys[1]? with | some key => pure key | none => throw (IO.userError "consumer missing")
  let made ← session.run producer [.word (w 1)] {executionFuel := 300000}
  match made with
  | .ok (.succeeded completion) =>
      match ← completion.session.run consumer [completion.value, .word (w 9)] {executionFuel := 300000} with
      | .ok (.succeeded applied) => match applied.value with
          | .word actual => assertTrue (actual == w 9) "coerced function lost original global"
          | _ => throw (IO.userError "coerced function returned the wrong value")
      | _ => throw (IO.userError "coerced function invocation failed")
  | _ => throw (IO.userError "function coercion did not complete")
  IO.println "source Core closed evidence and coercions GREEN"

end Tests.SourceCoreEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreEvidenceClosureSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreEvidenceClosure
open Solcore Frontend SourceInference SourceSemantics
abbrev Read := Tests.SourceCoreNamedBranch.Read
abbrev TypedNode := Tests.SourceCoreOperatorCalls.TypedNode
abbrev CallNode := Tests.SourceCoreEvidenceDirect.CallNode
def mark (trait : ProgramTraitId) (type : TypeSystem.Ty) : ProgramPredicate := ⟨trait, type, []⟩
abbrev ChooseShape := Tests.SourceCoreEvidenceDirect.ChooseShape
abbrev observeChoose := Tests.SourceCoreEvidenceDirect.observeChoose
abbrev observeCallNode := Tests.SourceCoreEvidenceDirect.observeCallNode
abbrev closureType (type : TypeSystem.Ty) : TypeSystem.Ty := .function .unit type
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

structure FactoryCall (source : TypedSource) (signature : ProgramFunctionSignature)
    (firstParameter secondParameter : TypeSystem.TypeParameterId)
    (firstType secondType : TypeSystem.Ty) (firstArgument secondArgument : ExpressionId) (trait : ProgramTraitId) where
  callee : TypedNode source (.function (.product firstType secondType) (closureType firstType))
  value : CallNode source (closureType firstType)
  requirement : RequirementId
  requirements : value.node.requirements = [requirement]
  name : String
  instantiation : Frontend.SourceInference.DeclarationInstantiation
  calleeForm : callee.node.form = .reference name (.declaration instantiation)
  form : value.node.form = .call callee.node.id [firstArgument, secondArgument] (.declaration instantiation)
  different : firstParameter ≠ secondParameter
  scheme : signature.scheme = ⟨[firstParameter, secondParameter], [mark trait (.parameter firstParameter)],
    .function (.product (.parameter firstParameter) (.parameter secondParameter)) (closureType (.parameter firstParameter))⟩
  inputs : signature.parameterTypes = [.parameter firstParameter, .parameter secondParameter]
  returns : signature.returnTypes = [closureType (.parameter firstParameter)]
  exact : instantiation = ⟨signature.id, [(secondParameter, secondType), (firstParameter, firstType)],
    .function (.product firstType secondType) (closureType firstType), [mark trait firstType], signature.parameterComptime, signature.returnComptime⟩

theorem FactoryCall.typed {source signature firstParameter secondParameter firstType secondType firstArgument secondArgument trait}
    (call : FactoryCall source signature firstParameter secondParameter firstType secondType firstArgument secondArgument trait)
    {context : SourceSemantics.Context} (member : signature ∈ context.signatures.functions)
    (firstFormed : TypeAdmissible context firstType) (secondFormed : TypeAdmissible context secondType)
    (firstTyped : ExpressionHasType source context firstArgument firstType)
    (secondTyped : ExpressionHasType source context secondArgument secondType)
    (required : RequirementProves context call.requirement (mark trait firstType)) :
    ExpressionHasType source context call.value.node.id (closureType firstType) := by
  have closureFormed : TypeAdmissible context (closureType firstType) := ⟨firstFormed.1, .function (.builtin .unit) (TypeAdmissible.typeWellScopedWithin (fun _ member => (TypeSystem.Ty.mem_freeVariables_function_iff _ _ _).mpr (.inr member)) firstFormed)⟩
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
    · simp [call.scheme, closureType, TypeSystem.ParameterSubstitution.apply, TypeSystem.ParameterSubstitution.lookup?, Ne.symm call.different]
    · simp [call.scheme, mark, ProgramPredicate.applyParameters, TypeSystem.ParameterSubstitution.apply, TypeSystem.ParameterSubstitution.lookup?, Ne.symm call.different]
  have application : DeclarationApplicationValid context call.instantiation [firstType, secondType] (closureType firstType) [mark trait firstType] := by
    refine .intro member valid ?_ ?_ ?_ ?_ ?_
    · simp [call.exact]
    · simp [call.exact, call.inputs, TypeSystem.ParameterSubstitution.apply, TypeSystem.ParameterSubstitution.lookup?, Ne.symm call.different]
    · simp [call.exact, call.returns, closureType, TypeSystem.Ty.productMany, TypeSystem.ParameterSubstitution.apply, TypeSystem.ParameterSubstitution.lookup?, Ne.symm call.different]
    · simp [call.exact, TypeSystem.Ty.productMany]
    · simp [call.exact]
  have callee : DirectDeclarationCalleeValid context source call.callee.node.id call.instantiation :=
    .intro (lookupExpression?_sound call.callee.found) call.calleeForm valid
      (call.callee.type.trans (by rw [call.exact])) call.callee.requirements call.callee.coercions
  have typed : ExpressionHasType source context call.value.node.id call.value.node.type := by
    refine .intro (lookupExpression?_sound call.value.found)
      (call.form ▸ ExpressionFormHasRawType.directCall callee application (.cons firstTyped (.cons secondTyped (.nil _))))
      call.value.raw closureFormed (call.value.type.symm ▸ closureFormed) ?_
    rw [call.requirements, call.value.coercions, call.value.type]
    exact .directCall (.intro (.nil _) (.nil _) (.cons required .nil) rfl rfl)
  exact Eq.mp (congrArg (fun type => ExpressionHasType source context call.value.node.id type) call.value.type) typed

structure RootShape (function : CheckedFunction) (signature generic : ProgramFunctionSignature)
    (firstParameter secondParameter : TypeSystem.TypeParameterId) (firstType secondType : TypeSystem.Ty) (trait : ProgramTraitId) where
  first : TypedBinder
  second : TypedBinder
  different : second.id ≠ first.id
  firstRead : Read function.typedBody first firstType
  secondRead : Read function.typedBody second secondType
  call : FactoryCall function.typedBody generic firstParameter secondParameter firstType secondType firstRead.node.id secondRead.node.id trait
  statement : StatementNode
  solved : SolvedRequirement
  solvedMember : solved ∈ function.solvedRequirements
  solvedId : solved.id = call.requirement
  solvedPredicate : solved.predicate = mark trait firstType
  noTemplates : sourceLocalSchemeTemplateIds function.typedBody = []
  inputs : function.typedBody.inputs = [first, second]
  firstScheme : first.scheme = .mono firstType
  secondScheme : second.scheme = .mono secondType
  firstRequirements : first.schemeRequirements = []
  secondRequirements : second.schemeRequirements = []
  roots : function.typedBody.roots = [.statement statement.id]
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some call.value.node.id)
  statementType : statement.type = closureType firstType

def RootShape.nodeList {function signature generic firstParameter secondParameter firstType secondType trait}
    (shape : RootShape function signature generic firstParameter secondParameter firstType secondType trait) : List Node :=
  [.expression shape.firstRead.node, .expression shape.secondRead.node, .expression shape.call.callee.node,
   .expression shape.call.value.node, .statement shape.statement]

theorem RootShape.statementTyping {function signature generic firstParameter secondParameter firstType secondType trait}
    (shape : RootShape function signature generic firstParameter secondParameter firstType secondType trait)
    (signatures : ProgramSignatures) (member : generic ∈ signatures.functions)
    (header : CheckedBodyHeaderWellFormed signatures signature function)
    (ledger : ScopedRequirementLedgerWellFormed (checkedBodyContext signatures signature function) function.typedBody)
    (inputTypes : signature.parameterTypes = [firstType, secondType])
    (returns : signature.returnTypes = [closureType firstType]) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.statement.id] := statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [returns]
  let facts : StatementFacts := {type := closureType firstType, hasValue := true, sawReturn := true, control := .returned}
  refine ⟨BodyFacts.singleton facts, rfl, ?_⟩
  intro lexical extension
  rw [shape.inputs, inputTypes] at extension
  cases extension with
  | cons firstScheme firstExtended rest =>
    cases rest with
    | cons secondScheme secondExtended rest =>
      cases rest
      have fields : lexical.signatures = signatures := by
        rw [secondExtended.context_fields.1, firstExtended.context_fields.1]
        rfl
      have types := StructuralSubstitution.TypesWellFormed.transportContext
        (secondExtended.context_fields.1.trans firstExtended.context_fields.1)
        (secondExtended.context_fields.2.2.1.trans firstExtended.context_fields.2.2.1)
        (secondExtended.context_fields.2.1.trans firstExtended.context_fields.2.1)
        header.parameter_types
      have firstFormed := TypeAdmissible.ofWellFormed (types firstType (by simp [inputTypes]))
      have secondFormed := TypeAdmissible.ofWellFormed (types secondType (by simp [inputTypes]))
      have currentLedger := ledger.transportContext
        (secondExtended.context_fields.1.trans firstExtended.context_fields.1)
        (secondExtended.context_fields.2.2.2.1.trans firstExtended.context_fields.2.2.2.1)
        (secondExtended.context_fields.2.2.2.2.trans firstExtended.context_fields.2.2.2.2)
      have rowMember : shape.solved ∈ lexical.solvedRequirements := by
        rw [secondExtended.context_fields.2.2.2.2, firstExtended.context_fields.2.2.2.2]
        exact shape.solvedMember
      have required : RequirementProves lexical shape.call.requirement (mark trait firstType) :=
        ⟨shape.solved, ⟨rowMember, shape.solvedId⟩, shape.solvedPredicate,
          currentLedger.ordinary_valid rowMember (by simp [shape.noTemplates])⟩
      have firstTyped := shape.firstRead.typed firstScheme shape.firstRequirements firstFormed
        (by cases secondExtended; exact .tail shape.different firstExtended.local_self)
        (by cases secondExtended; exact .tail shape.different firstExtended.local_scheme_requirements_self)
      have secondTyped := shape.secondRead.typed secondScheme shape.secondRequirements secondFormed
        secondExtended.local_self secondExtended.local_scheme_requirements_self
      have callTyped := shape.call.typed (fields ▸ member) firstFormed secondFormed firstTyped secondTyped required
      exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.statementFound)
        shape.statementForm callTyped shape.statementType)⟩


def observeFactoryCall (source : TypedSource) (signature : ProgramFunctionSignature)
    (firstParameter secondParameter : TypeSystem.TypeParameterId) (firstType secondType : TypeSystem.Ty)
    (firstArgument secondArgument : ExpressionId) (callee value : ExpressionNode) (trait : ProgramTraitId) :
    IO (FactoryCall source signature firstParameter secondParameter firstType secondType firstArgument secondArgument trait) := do
  let callee ← Tests.SourceCoreOperatorCalls.observeNode source callee (.function (.product firstType secondType) (closureType firstType))
  let value ← observeCallNode source value (closureType firstType)
  let [requirement] := value.node.requirements | throw (IO.userError "direct requirement")
  let ⟨requirements⟩ ← observed (value.node.requirements = [requirement]) "direct requirements"
  let .reference name (.declaration instantiation) := callee.node.form | throw (IO.userError "generic direct callee")
  let ⟨calleeForm⟩ ← observed (callee.node.form = .reference name (.declaration instantiation)) "generic direct calleeForm"
  let ⟨form⟩ ← observed (value.node.form = .call callee.node.id [firstArgument, secondArgument] (.declaration instantiation)) "generic direct form"
  let ⟨different⟩ ← observed (firstParameter ≠ secondParameter) "generic direct different"
  let ⟨scheme⟩ ← observed (signature.scheme = ⟨[firstParameter, secondParameter], [mark trait (.parameter firstParameter)], .function (.product (.parameter firstParameter) (.parameter secondParameter)) (closureType (.parameter firstParameter))⟩) "generic direct scheme"
  let ⟨inputs⟩ ← observed (signature.parameterTypes = [.parameter firstParameter, .parameter secondParameter]) "generic direct inputs"
  let ⟨returns⟩ ← observed (signature.returnTypes = [closureType (.parameter firstParameter)]) "generic direct returns"
  let ⟨exact⟩ ← observed (instantiation = ⟨signature.id, [(secondParameter, secondType), (firstParameter, firstType)], .function (.product firstType secondType) (closureType firstType), [mark trait firstType], signature.parameterComptime, signature.returnComptime⟩) "generic direct exact"
  return {callee, value, requirement, requirements, name, instantiation, calleeForm, form, different, scheme, inputs, returns, exact}

def observeRoot (function : CheckedFunction) (signature generic : ProgramFunctionSignature)
    (firstParameter secondParameter : TypeSystem.TypeParameterId) (firstType secondType : TypeSystem.Ty) (trait : ProgramTraitId) :
    IO (RootShape function signature generic firstParameter secondParameter firstType secondType trait) := do
  let [first, second] := function.typedBody.inputs | throw (IO.userError "root inputs")
  let [.expression readFirst, .expression readSecond, .expression callee, .expression value, .statement statement] := function.typedBody.nodes
    | throw (IO.userError "root nodes")
  let firstRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody first readFirst firstType
  let secondRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody second readSecond secondType
  let call ← observeFactoryCall function.typedBody generic firstParameter secondParameter firstType secondType firstRead.node.id secondRead.node.id callee value trait
  let ⟨different⟩ ← observed (second.id ≠ first.id) "generic root different"
  match rows : function.solvedRequirements with
  | [solved] =>
    let solvedMember : solved ∈ function.solvedRequirements := by simp [rows]
    let ⟨solvedId⟩ ← observed (solved.id = call.requirement) "call solved identity"
    let ⟨solvedPredicate⟩ ← observed (solved.predicate = mark trait firstType) "call solved predicate"
    let ⟨noTemplates⟩ ← observed (sourceLocalSchemeTemplateIds function.typedBody = []) "no templates"
    let ⟨inputs⟩ ← observed (function.typedBody.inputs = [first, second]) "generic root inputs"
    let ⟨firstScheme⟩ ← observed (first.scheme = .mono firstType) "generic root firstScheme"
    let ⟨secondScheme⟩ ← observed (second.scheme = .mono secondType) "generic root secondScheme"
    let ⟨firstRequirements⟩ ← observed (first.schemeRequirements = []) "generic root firstRequirements"
    let ⟨secondRequirements⟩ ← observed (second.schemeRequirements = []) "generic root secondRequirements"
    let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "generic root roots"
    let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "generic root statementFound"
    let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some call.value.node.id)) "generic root statementForm"
    let ⟨statementType⟩ ← observed (statement.type = closureType firstType) "generic root statementType"
    return {first, second, firstRead, secondRead, call, statement, different, solved, solvedMember, solvedId, solvedPredicate, noTemplates, inputs, firstScheme, secondScheme, firstRequirements, secondRequirements, roots, statementFound, statementForm, statementType}
  | _ => throw (IO.userError "call ledger")

structure FactoryShape (function : CheckedFunction) (signature generic : ProgramFunctionSignature)
    (firstParameter secondParameter : TypeSystem.TypeParameterId) (firstType secondType : TypeSystem.Ty) (trait : ProgramTraitId) where
  first : TypedBinder
  second : TypedBinder
  different : second.id ≠ first.id
  firstRead : Read function.typedBody first firstType
  secondRead : Read function.typedBody second secondType
  call : Tests.SourceCoreEvidenceDirect.DirectCall function.typedBody generic firstParameter secondParameter firstType secondType firstRead.node.id secondRead.node.id trait
  statement : StatementNode
  expression : ExpressionNode
  outerReturn : StatementNode
  solved : SolvedRequirement
  solvedMember : solved ∈ function.solvedRequirements
  solvedId : solved.id = call.requirement
  solvedPredicate : solved.predicate = mark trait firstType
  noTemplates : sourceLocalSchemeTemplateIds function.typedBody = []
  inputs : function.typedBody.inputs = [first, second]
  firstScheme : first.scheme = .mono firstType
  secondScheme : second.scheme = .mono secondType
  firstRequirements : first.schemeRequirements = []
  secondRequirements : second.schemeRequirements = []
  roots : function.typedBody.roots = [.statement outerReturn.id]
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some call.value.node.id)
  statementType : statement.type = firstType

  expressionFound : function.typedBody.lookupExpression? expression.id = some expression
  lambda : expression.form = .lambda [] firstType [statement.id]
  expressionRaw : expression.rawType = closureType firstType
  expressionType : expression.type = closureType firstType
  requirements : expression.requirements = []
  coercions : expression.coercions = []
  outerFound : function.typedBody.lookupStatement? outerReturn.id = some outerReturn
  outerForm : outerReturn.form = .returnStmt (some expression.id)
  outerType : outerReturn.type = closureType firstType

def FactoryShape.nodeList {function signature generic firstParameter secondParameter firstType secondType trait}
    (shape : FactoryShape function signature generic firstParameter secondParameter firstType secondType trait) : List Node :=
  [.expression shape.firstRead.node, .expression shape.secondRead.node, .expression shape.call.callee.node,
   .expression shape.call.value.node, .statement shape.statement, .expression shape.expression, .statement shape.outerReturn]

theorem FactoryShape.statementTyping {function signature generic firstParameter secondParameter firstType secondType trait}
    (shape : FactoryShape function signature generic firstParameter secondParameter firstType secondType trait)
    (signatures : ProgramSignatures) (member : generic ∈ signatures.functions)
    (header : CheckedBodyHeaderWellFormed signatures signature function)
    (ledger : ScopedRequirementLedgerWellFormed (checkedBodyContext signatures signature function) function.typedBody)
    (inputTypes : signature.parameterTypes = [firstType, secondType])
    (returns : signature.returnTypes = [closureType firstType]) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.outerReturn.id] := statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [returns]
  let facts : StatementFacts := {type := closureType firstType, hasValue := true, sawReturn := true, control := .returned}
  refine ⟨BodyFacts.singleton facts, rfl, ?_⟩
  intro lexical extension
  rw [shape.inputs, inputTypes] at extension
  cases extension with
  | cons firstScheme firstExtended rest =>
    cases rest with
    | cons secondScheme secondExtended rest =>
      cases rest
      have fields : lexical.signatures = signatures := by
        rw [secondExtended.context_fields.1, firstExtended.context_fields.1]
        rfl
      have types := StructuralSubstitution.TypesWellFormed.transportContext
        (secondExtended.context_fields.1.trans firstExtended.context_fields.1)
        (secondExtended.context_fields.2.2.1.trans firstExtended.context_fields.2.2.1)
        (secondExtended.context_fields.2.1.trans firstExtended.context_fields.2.1)
        header.parameter_types
      have firstFormed := TypeAdmissible.ofWellFormed (types firstType (by simp [inputTypes]))
      have secondFormed := TypeAdmissible.ofWellFormed (types secondType (by simp [inputTypes]))
      have currentLedger := ledger.transportContext
        (secondExtended.context_fields.1.trans firstExtended.context_fields.1)
        (secondExtended.context_fields.2.2.2.1.trans firstExtended.context_fields.2.2.2.1)
        (secondExtended.context_fields.2.2.2.2.trans firstExtended.context_fields.2.2.2.2)
      have rowMember : shape.solved ∈ lexical.solvedRequirements := by
        rw [secondExtended.context_fields.2.2.2.2, firstExtended.context_fields.2.2.2.2]
        exact shape.solvedMember
      have required : RequirementProves lexical shape.call.requirement (mark trait firstType) :=
        ⟨shape.solved, ⟨rowMember, shape.solvedId⟩, shape.solvedPredicate,
          currentLedger.ordinary_valid rowMember (by simp [shape.noTemplates])⟩
      have firstTyped := shape.firstRead.typed firstScheme shape.firstRequirements firstFormed
        (by cases secondExtended; exact .tail shape.different firstExtended.local_self)
        (by cases secondExtended; exact .tail shape.different firstExtended.local_scheme_requirements_self)
      have secondTyped := shape.secondRead.typed secondScheme shape.secondRequirements secondFormed
        secondExtended.local_self secondExtended.local_scheme_requirements_self
      have callTyped := shape.call.typed (fields ▸ member) firstFormed secondFormed firstTyped secondTyped required
      have callable : TypeAdmissible lexical (closureType firstType) :=
        ⟨firstFormed.1, .function (.builtin .unit) (TypeAdmissible.typeWellScopedWithin (fun _ member => (TypeSystem.Ty.mem_freeVariables_function_iff _ _ _).mpr (.inr member)) firstFormed)⟩
      have lambdaTyped : ExpressionHasType function.typedBody lexical shape.expression.id (closureType firstType) := by
        rw [← shape.expressionType]
        refine .intro (lookupExpression?_sound shape.expressionFound)
          (shape.lambda ▸ ExpressionFormHasRawType.lambda (by simp) (.nil _)
            (.singleton (.returnValue (lookupStatement?_sound shape.statementFound)
              shape.statementForm callTyped shape.statementType))
            (by exact ⟨rfl, rfl, .inl ⟨rfl, rfl⟩⟩)) shape.expressionRaw callable (shape.expressionType ▸ callable) ?_
        rw [shape.requirements, shape.coercions, shape.expressionType]
        exact .ordinary (by intro id member; cases member) (.nil _) rfl
      exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.outerFound)
        shape.outerForm lambdaTyped shape.outerType)⟩


def observeFactory (function : CheckedFunction) (signature generic : ProgramFunctionSignature)
    (firstParameter secondParameter : TypeSystem.TypeParameterId) (firstType secondType : TypeSystem.Ty) (trait : ProgramTraitId) :
    IO (FactoryShape function signature generic firstParameter secondParameter firstType secondType trait) := do
  let [first, second] := function.typedBody.inputs | throw (IO.userError "root inputs")
  let [.expression readFirst, .expression readSecond, .expression callee, .expression value, .statement statement, .expression expression, .statement outerReturn] := function.typedBody.nodes
    | throw (IO.userError "root nodes")
  let firstRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody first readFirst firstType
  let secondRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody second readSecond secondType
  let call ← Tests.SourceCoreEvidenceDirect.observeDirect function.typedBody generic firstParameter secondParameter firstType secondType firstRead.node.id secondRead.node.id callee value trait
  let ⟨different⟩ ← observed (second.id ≠ first.id) "generic root different"
  match rows : function.solvedRequirements with
  | [solved] =>
    let solvedMember : solved ∈ function.solvedRequirements := by simp [rows]
    let ⟨solvedId⟩ ← observed (solved.id = call.requirement) "call solved identity"
    let ⟨solvedPredicate⟩ ← observed (solved.predicate = mark trait firstType) "call solved predicate"
    let ⟨noTemplates⟩ ← observed (sourceLocalSchemeTemplateIds function.typedBody = []) "no templates"
    let ⟨inputs⟩ ← observed (function.typedBody.inputs = [first, second]) "generic root inputs"
    let ⟨firstScheme⟩ ← observed (first.scheme = .mono firstType) "generic root firstScheme"
    let ⟨secondScheme⟩ ← observed (second.scheme = .mono secondType) "generic root secondScheme"
    let ⟨firstRequirements⟩ ← observed (first.schemeRequirements = []) "generic root firstRequirements"
    let ⟨secondRequirements⟩ ← observed (second.schemeRequirements = []) "generic root secondRequirements"
    let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement outerReturn.id]) "generic root roots"
    let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "generic root statementFound"
    let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some call.value.node.id)) "generic root statementForm"
    let ⟨statementType⟩ ← observed (statement.type = firstType) "generic root statementType"
    let ⟨expressionFound⟩ ← observed (function.typedBody.lookupExpression? expression.id = some expression) "factory expressionFound"
    let ⟨lambda⟩ ← observed (expression.form = .lambda [] firstType [statement.id]) "factory lambda"
    let ⟨expressionRaw⟩ ← observed (expression.rawType = closureType firstType) "factory expressionRaw"
    let ⟨expressionType⟩ ← observed (expression.type = closureType firstType) "factory expressionType"
    let ⟨requirements⟩ ← observed (expression.requirements = []) "factory requirements"
    let ⟨coercions⟩ ← observed (expression.coercions = []) "factory coercions"
    let ⟨outerFound⟩ ← observed (function.typedBody.lookupStatement? outerReturn.id = some outerReturn) "factory outerFound"
    let ⟨outerForm⟩ ← observed (outerReturn.form = .returnStmt (some expression.id)) "factory outerForm"
    let ⟨outerType⟩ ← observed (outerReturn.type = closureType firstType) "factory outerType"
    return {expression, outerReturn, expressionFound, lambda, expressionRaw, expressionType, requirements, coercions, outerFound, outerForm, outerType, first, second, firstRead, secondRead, call, statement, different, solved, solvedMember, solvedId, solvedPredicate, noTemplates, inputs, firstScheme, secondScheme, firstRequirements, secondRequirements, roots, statementFound, statementForm, statementType}
  | _ => throw (IO.userError "call ledger")

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}", "impl Mark<Bool> {}",
    "function choose<A, B>(a: A, b: B) returns (A) where A: Mark { return a; }",
    "function factory<A, B>(a: A, b: B) returns (function() returns (A)) where A: Mark { return lam() -> A { return choose(a, b); }; }",
    "function wordRoot(value: Word, flag: Bool) returns (function() returns (Word)) { return factory(value, flag); }",
    "function boolRoot(flag: Bool, value: Word) returns (function() returns (Bool)) { return factory(flag, value); }"]}] }

structure CheckedFixture where
  program : CheckedProgram
  checked : checkProgram workspace 1000 = .ok program
  wellFormed : ProgramWellFormed (Program.ofChecked program)
  trait : ProgramTraitId
  chooseFunction : CheckedFunction
  chooseSignature : ProgramFunctionSignature
  factoryFunction : CheckedFunction
  factorySignature : ProgramFunctionSignature
  wordFunction : CheckedFunction
  wordSignature : ProgramFunctionSignature
  boolFunction : CheckedFunction
  boolSignature : ProgramFunctionSignature
  functions : program.functions = [chooseFunction, factoryFunction, wordFunction, boolFunction]
  signatures : program.signatures.functions = [chooseSignature, factorySignature, wordSignature, boolSignature]
  methods : program.methods = []
  chooseDeclaration : chooseFunction.declaration = chooseSignature.id
  factoryDeclaration : factoryFunction.declaration = factorySignature.id
  wordDeclaration : wordFunction.declaration = wordSignature.id
  boolDeclaration : boolFunction.declaration = boolSignature.id
  chooseFactory : chooseSignature.id ≠ factorySignature.id
  chooseWord : chooseSignature.id ≠ wordSignature.id
  chooseBool : chooseSignature.id ≠ boolSignature.id
  factoryWord : factorySignature.id ≠ wordSignature.id
  factoryBool : factorySignature.id ≠ boolSignature.id
  wordBool : wordSignature.id ≠ boolSignature.id
  chooseShape : ChooseShape chooseFunction chooseSignature trait
  factoryFirstParameter : TypeSystem.TypeParameterId
  factorySecondParameter : TypeSystem.TypeParameterId
  factoryScheme : factorySignature.scheme = ⟨[factoryFirstParameter, factorySecondParameter], [mark trait (.parameter factoryFirstParameter)], .function (.product (.parameter factoryFirstParameter) (.parameter factorySecondParameter)) (closureType (.parameter factoryFirstParameter))⟩
  factoryShape : FactoryShape factoryFunction factorySignature chooseSignature chooseShape.firstParameter chooseShape.secondParameter (.parameter factoryFirstParameter) (.parameter factorySecondParameter) trait
  wordShape : RootShape wordFunction wordSignature factorySignature factoryFirstParameter factorySecondParameter .word .bool trait
  boolShape : RootShape boolFunction boolSignature factorySignature factoryFirstParameter factorySecondParameter .bool .word trait
  chooseNodes : chooseFunction.typedBody.nodes = chooseShape.nodeList
  factoryInputTypes : factorySignature.parameterTypes = [(.parameter factoryFirstParameter), (.parameter factorySecondParameter)]
  factoryReturns : factorySignature.returnTypes = [closureType (.parameter factoryFirstParameter)]
  factoryNodes : factoryFunction.typedBody.nodes = factoryShape.nodeList
  wordInputTypes : wordSignature.parameterTypes = [.word, .bool]
  wordReturns : wordSignature.returnTypes = [closureType .word]
  wordNodes : wordFunction.typedBody.nodes = wordShape.nodeList
  boolInputTypes : boolSignature.parameterTypes = [.bool, .word]
  boolReturns : boolSignature.returnTypes = [closureType .bool]
  boolNodes : boolFunction.typedBody.nodes = boolShape.nodeList

private theorem checkedHeader {program : CheckedProgram} (checked : checkProgram workspace 1000 = .ok program)
    {function signature} (member : function ∈ program.functions) (signatureMember : signature ∈ program.signatures.functions)
    (accepted : checkFunctionBody program.environment program.signatures signature 1000 = .ok function) :
    CheckedBodyHeaderWellFormed program.signatures signature function := by
  obtain ⟨other, otherMember, header⟩ := checkedFunctionHeaderWellFormed_ofCheckProgram checked member
  have same : other = signature := eq_of_mem_of_nodup_map
    (SignatureCatalogWellFormed.ofCheckProgram checked).function_ids otherMember signatureMember
    (header.declaration_eq.symm.trans (checkFunctionBody_success_declaration accepted))
  exact same ▸ header

def checkedFixture : IO CheckedFixture := do
  match checked : checkProgram workspace 1000 with
  | .error error => throw (IO.userError (reprStr error))
  | .ok program =>
    match functions : program.functions, signatures : program.signatures.functions with
    | [chooseFunction, factoryFunction, wordFunction, boolFunction], [chooseSignature, factorySignature, wordSignature, boolSignature] =>
      let [predicate] := chooseSignature.scheme.predicates | throw (IO.userError "choose predicate")
      let trait := predicate.trait
      let chooseShape ← observeChoose chooseFunction chooseSignature trait
      let [factoryFirstParameter, factorySecondParameter] := factorySignature.scheme.parameters | throw (IO.userError "factory parameters")
      let ⟨factoryScheme⟩ ← observed (factorySignature.scheme = ⟨[factoryFirstParameter, factorySecondParameter], [mark trait (.parameter factoryFirstParameter)], .function (.product (.parameter factoryFirstParameter) (.parameter factorySecondParameter)) (closureType (.parameter factoryFirstParameter))⟩) "factory scheme"
      let factoryShape ← observeFactory factoryFunction factorySignature chooseSignature chooseShape.firstParameter chooseShape.secondParameter (.parameter factoryFirstParameter) (.parameter factorySecondParameter) trait
      let wordShape ← observeRoot wordFunction wordSignature factorySignature factoryFirstParameter factorySecondParameter .word .bool trait
      let boolShape ← observeRoot boolFunction boolSignature factorySignature factoryFirstParameter factorySecondParameter .bool .word trait
      let ⟨methods⟩ ← observed (program.methods = []) "fixture methods"
      let ⟨chooseDeclaration⟩ ← observed (chooseFunction.declaration = chooseSignature.id) "choose declaration"
      let ⟨factoryDeclaration⟩ ← observed (factoryFunction.declaration = factorySignature.id) "factory declaration"
      let ⟨wordDeclaration⟩ ← observed (wordFunction.declaration = wordSignature.id) "word declaration"
      let ⟨boolDeclaration⟩ ← observed (boolFunction.declaration = boolSignature.id) "bool declaration"
      let ⟨chooseFactory⟩ ← observed (chooseSignature.id ≠ factorySignature.id) "chooseFactory distinct"
      let ⟨chooseWord⟩ ← observed (chooseSignature.id ≠ wordSignature.id) "chooseWord distinct"
      let ⟨chooseBool⟩ ← observed (chooseSignature.id ≠ boolSignature.id) "chooseBool distinct"
      let ⟨factoryWord⟩ ← observed (factorySignature.id ≠ wordSignature.id) "factoryWord distinct"
      let ⟨factoryBool⟩ ← observed (factorySignature.id ≠ boolSignature.id) "factoryBool distinct"
      let ⟨wordBool⟩ ← observed (wordSignature.id ≠ boolSignature.id) "wordBool distinct"
      let ⟨chooseNodes⟩ ← observed (chooseFunction.typedBody.nodes = chooseShape.nodeList) "choose nodes"
      let ⟨factoryInputTypes⟩ ← observed (factorySignature.parameterTypes = [(.parameter factoryFirstParameter), (.parameter factorySecondParameter)]) "factory original input types"
      let ⟨factoryReturns⟩ ← observed (factorySignature.returnTypes = [closureType (.parameter factoryFirstParameter)]) "factory original returns"
      let ⟨factoryNodes⟩ ← observed (factoryFunction.typedBody.nodes = factoryShape.nodeList) "factory nodes"
      let ⟨wordInputTypes⟩ ← observed (wordSignature.parameterTypes = [.word, .bool]) "word original input types"
      let ⟨wordReturns⟩ ← observed (wordSignature.returnTypes = [closureType .word]) "word original returns"
      let ⟨wordNodes⟩ ← observed (wordFunction.typedBody.nodes = wordShape.nodeList) "word nodes"
      let ⟨boolInputTypes⟩ ← observed (boolSignature.parameterTypes = [.bool, .word]) "bool original input types"
      let ⟨boolReturns⟩ ← observed (boolSignature.returnTypes = [closureType .bool]) "bool original returns"
      let ⟨boolNodes⟩ ← observed (boolFunction.typedBody.nodes = boolShape.nodeList) "bool nodes"
      let deep : CheckedProgramBodiesHaveStatementTyping program 1000 := {
        functions := by
          intro actual member candidate candidateMember accepted
          have identity := checkFunctionBody_success_declaration accepted
          have header := checkedHeader checked member candidateMember accepted
          have ledger := SourceInferenceSoundness.checkFunctionBody_success_scopedRequirementLedgerWellFormed_bodyContext
            (checkProgram_success_signature_formation checked) candidateMember accepted
          simp only [functions, List.mem_cons, List.not_mem_nil, or_false] at member
          simp only [signatures, List.mem_cons, List.not_mem_nil, or_false] at candidateMember
          rcases member with rfl | rfl | rfl | rfl <;> rcases candidateMember with rfl | rfl | rfl | rfl
          · exact chooseShape.statementTyping program.signatures
          · exact False.elim (chooseFactory (chooseDeclaration.symm.trans identity))
          · exact False.elim (chooseWord (chooseDeclaration.symm.trans identity))
          · exact False.elim (chooseBool (chooseDeclaration.symm.trans identity))
          · exact False.elim (chooseFactory (identity.symm.trans factoryDeclaration))
          · exact factoryShape.statementTyping program.signatures (by simp [signatures]) header ledger factoryInputTypes factoryReturns
          · exact False.elim (factoryWord (factoryDeclaration.symm.trans identity))
          · exact False.elim (factoryBool (factoryDeclaration.symm.trans identity))
          · exact False.elim (chooseWord (identity.symm.trans wordDeclaration))
          · exact False.elim (factoryWord (identity.symm.trans wordDeclaration))
          · exact wordShape.statementTyping program.signatures (by simp [signatures]) header ledger wordInputTypes wordReturns
          · exact False.elim (wordBool (wordDeclaration.symm.trans identity))
          · exact False.elim (chooseBool (identity.symm.trans boolDeclaration))
          · exact False.elim (factoryBool (identity.symm.trans boolDeclaration))
          · exact False.elim (wordBool (identity.symm.trans boolDeclaration))
          · exact boolShape.statementTyping program.signatures (by simp [signatures]) header ledger boolInputTypes boolReturns
        methods := by intro method member; simp only [methods, List.not_mem_nil] at member }
      return {wellFormed := programWellFormed_ofCheckProgram_statements checked deep, program, checked, trait, chooseFunction, factoryFunction, wordFunction, boolFunction, chooseSignature, factorySignature, wordSignature, boolSignature, functions, signatures, methods, chooseDeclaration, factoryDeclaration, wordDeclaration, boolDeclaration, chooseFactory, chooseWord, chooseBool, factoryWord, factoryBool, wordBool, chooseShape, factoryFirstParameter, factorySecondParameter, factoryScheme, factoryShape, wordShape, boolShape, chooseNodes, factoryInputTypes, factoryReturns, factoryNodes, wordInputTypes, wordReturns, wordNodes, boolInputTypes, boolReturns, boolNodes}
    | _, _ => throw (IO.userError "evidence direct declarations")
end Tests.SourceCoreEvidenceClosure
end

section
-- leanmerge: from Solcore.Test.SourceCoreEvidenceClosureFixture
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreEvidenceClosure
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
  let seeds := [SourceCompiler.Seed.declaration checked.wordSignature.id, SourceCompiler.Seed.declaration checked.boolSignature.id]
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
    (CoreLowering.CallableNamedCanonicalOrder.retainedInstantiation row) header
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
    instantiation := CallableNamedCanonicalOrder.retainedInstantiation row
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
and original source declaration. Public roots additionally retain an entry. -/
structure ObservedRow (fixture : CompiledFixture) (signature : ProgramFunctionSignature) where
  row : SourceSpecialization.SpecializedFunction
  member : row ∈ fixture.recipe.compiled.validationPlan.specializations
  sourceOwner : row.function.typedBody.owner = signature.id
  scalarRange : row.parameterSubstitution.all (fun entry => decide (entry.2 = .word ∨ entry.2 = .bool)) = true
  keyOwner : row.key.declaration = signature.id
  ordinary : row.function.returnComptime = false
  inputsOrdinary : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false
  target : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
    (CallableNamedCanonicalOrder.retainedInstantiation row) = .ok row.key
  global : SourceCoreCalls.Signature
  index : Nat
  slot : CallableNamedMetadata.Slot fixture.recipe.compiled.indexed.base.globals index global
  globalKey : global.key = row.key

structure ObservedRoot (fixture : CompiledFixture) (signature : ProgramFunctionSignature) extends ObservedRow fixture signature where
  entry : SourceCoreCallableIndexedPrograms.Entry fixture.recipe.compiled.indexed.layouts
  entryMember : entry ∈ fixture.recipe.compiled.indexed.entries
  entryKey : entry.key = row.key

private def observeTarget (fixture : CompiledFixture) (row : SourceSpecialization.SpecializedFunction) :
    IO (PLift (SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedCanonicalOrder.retainedInstantiation row) = .ok row.key)) := do
  match accepted : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedCanonicalOrder.retainedInstantiation row) with
  | .error error => throw (IO.userError (reprStr error))
  | .ok key =>
    let ⟨same⟩ ← observed (key = row.key) "reuse exact key"
    return ⟨by rw [accepted, same]⟩

def observeRow (fixture : CompiledFixture) (signature : ProgramFunctionSignature) (arguments : List TypeSystem.Ty) :
    IO (ObservedRow fixture signature) := do
  match found : fixture.recipe.compiled.validationPlan.specializations.find?
      (fun row => decide (row.function.typedBody.owner = signature.id ∧ row.key.arguments = arguments)) with
  | none => throw (IO.userError "reuse specialization missing")
  | some row =>
    let ⟨sourceOwner⟩ ← observed (row.function.typedBody.owner = signature.id) "reuse source owner"
    let ⟨scalarRange⟩ ← observed (row.parameterSubstitution.all (fun entry => decide (entry.2 = .word ∨ entry.2 = .bool)) = true) "generic complete raw range"
    let ⟨keyOwner⟩ ← observed (row.key.declaration = signature.id) "generic row key owner"
    let ⟨ordinary⟩ ← observed (row.function.returnComptime = false) "reuse return marker"
    let ⟨ordinaryInputs⟩ ← observed (row.function.typedBody.inputs.all (fun binder => !binder.comptime) = true) "reuse parameter markers"
    let ⟨target⟩ ← observeTarget fixture row
    match slot : fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun item => decide (item.1.key = row.key)) with
    | [(global, index)] =>
      let ⟨globalKey⟩ ← observed (global.key = row.key) "reuse global key"
      return {
        row := row
        member := List.mem_of_find?_eq_some found
        sourceOwner := sourceOwner
        scalarRange := scalarRange
        keyOwner := keyOwner
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
        }
    | _ => throw (IO.userError "reuse unique global slot")


def observeRootRow (fixture : CompiledFixture) (signature : ProgramFunctionSignature) : IO (ObservedRoot fixture signature) := do
  let row ← observeRow fixture signature []
  match entryFound : fixture.recipe.compiled.indexed.entries.find? (fun entry => decide (entry.key = row.row.key)) with
  | none => throw (IO.userError "public root entry missing")
  | some entry =>
    let ⟨entryKey⟩ ← observed (entry.key = row.row.key) "public root entry key"
    return {toObservedRow := row, entry, entryMember := List.mem_of_find?_eq_some entryFound, entryKey}

structure SelectedShape (function : CheckedFunction) (firstType secondType : TypeSystem.Ty) where
  first : TypedBinder
  second : TypedBinder
  read : Read function.typedBody first firstType
  statement : StatementNode
  inputs : function.typedBody.inputs = [first, second]
  firstScheme : first.scheme = .mono firstType
  secondScheme : second.scheme = .mono secondType
  firstRequirements : first.schemeRequirements = []
  secondRequirements : second.schemeRequirements = []
  roots : function.typedBody.roots = [.statement statement.id]
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some read.node.id)
  statementType : statement.type = firstType
  resultType : function.inferredBodyType = firstType

def SelectedShape.nodeList {function firstType secondType} (shape : SelectedShape function firstType secondType) : List Node :=
  [.expression shape.read.node, .statement shape.statement]

def observeSelected (function : CheckedFunction) (firstType secondType : TypeSystem.Ty) : IO (SelectedShape function firstType secondType) := do
  let [first, second] := function.typedBody.inputs | throw (IO.userError "generic selected inputs")
  let [.expression node, .statement statement] := function.typedBody.nodes | throw (IO.userError "generic selected nodes")
  let read ← Tests.SourceCoreNamedBranch.observeRead function.typedBody first node firstType
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [first, second]) "selected inputs"
  let ⟨firstScheme⟩ ← observed (first.scheme = .mono firstType) "selected firstScheme"
  let ⟨secondScheme⟩ ← observed (second.scheme = .mono secondType) "selected secondScheme"
  let ⟨firstRequirements⟩ ← observed (first.schemeRequirements = []) "selected firstRequirements"
  let ⟨secondRequirements⟩ ← observed (second.schemeRequirements = []) "selected secondRequirements"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "selected roots"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "selected statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some read.node.id)) "selected statementForm"
  let ⟨statementType⟩ ← observed (statement.type = firstType) "selected statementType"
  let ⟨resultType⟩ ← observed (function.inferredBodyType = firstType) "selected resultType"
  return {first, second, read, statement, inputs, firstScheme, secondScheme, firstRequirements, secondRequirements, roots, statementFound, statementForm, statementType, resultType}

structure ObservedProgram (fixture : CompiledFixture) where
  wordRow : ObservedRoot fixture fixture.wordSignature
  boolRow : ObservedRoot fixture fixture.boolSignature
  factoryWordRow : ObservedRow fixture fixture.factorySignature
  factoryBoolRow : ObservedRow fixture fixture.factorySignature
  chooseWordRow : ObservedRow fixture fixture.chooseSignature
  chooseBoolRow : ObservedRow fixture fixture.chooseSignature
  globalsLength : fixture.recipe.compiled.indexed.base.globals.length = 6
  indexCoverage : (List.range 6).all (fun index => decide (index ∈ [wordRow.index, boolRow.index, factoryWordRow.index, factoryBoolRow.index, chooseWordRow.index, chooseBoolRow.index])) = true
  wordBool : wordRow.index ≠ boolRow.index
  wordFactoryWord : wordRow.index ≠ factoryWordRow.index
  wordFactoryBool : wordRow.index ≠ factoryBoolRow.index
  wordChooseWord : wordRow.index ≠ chooseWordRow.index
  wordChooseBool : wordRow.index ≠ chooseBoolRow.index
  boolFactoryWord : boolRow.index ≠ factoryWordRow.index
  boolFactoryBool : boolRow.index ≠ factoryBoolRow.index
  boolChooseWord : boolRow.index ≠ chooseWordRow.index
  boolChooseBool : boolRow.index ≠ chooseBoolRow.index
  factoryWordFactoryBool : factoryWordRow.index ≠ factoryBoolRow.index
  factoryWordChooseWord : factoryWordRow.index ≠ chooseWordRow.index
  factoryWordChooseBool : factoryWordRow.index ≠ chooseBoolRow.index
  factoryBoolChooseWord : factoryBoolRow.index ≠ chooseWordRow.index
  factoryBoolChooseBool : factoryBoolRow.index ≠ chooseBoolRow.index
  chooseWordChooseBool : chooseWordRow.index ≠ chooseBoolRow.index
  wordShape : RootShape wordRow.row.function fixture.wordSignature fixture.factorySignature fixture.factoryFirstParameter fixture.factorySecondParameter .word .bool fixture.trait
  boolShape : RootShape boolRow.row.function fixture.boolSignature fixture.factorySignature fixture.factoryFirstParameter fixture.factorySecondParameter .bool .word fixture.trait
  factoryWordShape : FactoryShape factoryWordRow.row.function fixture.factorySignature fixture.chooseSignature fixture.chooseShape.firstParameter fixture.chooseShape.secondParameter .word .bool fixture.trait
  factoryBoolShape : FactoryShape factoryBoolRow.row.function fixture.factorySignature fixture.chooseSignature fixture.chooseShape.firstParameter fixture.chooseShape.secondParameter .bool .word fixture.trait
  chooseWordShape : SelectedShape chooseWordRow.row.function .word .bool
  chooseBoolShape : SelectedShape chooseBoolRow.row.function .bool .word
  wordNodes : wordRow.row.function.typedBody.nodes = wordShape.nodeList
  boolNodes : boolRow.row.function.typedBody.nodes = boolShape.nodeList
  factoryWordNodes : factoryWordRow.row.function.typedBody.nodes = factoryWordShape.nodeList
  factoryBoolNodes : factoryBoolRow.row.function.typedBody.nodes = factoryBoolShape.nodeList
  chooseWordNodes : chooseWordRow.row.function.typedBody.nodes = chooseWordShape.nodeList
  chooseBoolNodes : chooseBoolRow.row.function.typedBody.nodes = chooseBoolShape.nodeList
  wordResultType : wordRow.row.function.inferredBodyType = closureType .word
  boolResultType : boolRow.row.function.inferredBodyType = closureType .bool
  factoryWordResultType : factoryWordRow.row.function.inferredBodyType = closureType .word
  factoryBoolResultType : factoryBoolRow.row.function.inferredBodyType = closureType .bool
  wordKey : wordRow.row.key = ⟨fixture.wordSignature.id, []⟩
  boolKey : boolRow.row.key = ⟨fixture.boolSignature.id, []⟩
  factoryWordKey : factoryWordRow.row.key = ⟨fixture.factorySignature.id, [.word, .bool]⟩
  factoryBoolKey : factoryBoolRow.row.key = ⟨fixture.factorySignature.id, [.bool, .word]⟩
  chooseWordKey : chooseWordRow.row.key = ⟨fixture.chooseSignature.id, [.word, .bool]⟩
  chooseBoolKey : chooseBoolRow.row.key = ⟨fixture.chooseSignature.id, [.bool, .word]⟩
  wordParameters : wordRow.row.parameterSubstitution = []
  boolParameters : boolRow.row.parameterSubstitution = []
  factoryWordParameters : factoryWordRow.row.parameterSubstitution = [(fixture.factoryFirstParameter, .word), (fixture.factorySecondParameter, .bool)]
  factoryBoolParameters : factoryBoolRow.row.parameterSubstitution = [(fixture.factoryFirstParameter, .bool), (fixture.factorySecondParameter, .word)]
  chooseWordParameters : chooseWordRow.row.parameterSubstitution = [(fixture.chooseShape.firstParameter, .word), (fixture.chooseShape.secondParameter, .bool)]
  chooseBoolParameters : chooseBoolRow.row.parameterSubstitution = [(fixture.chooseShape.firstParameter, .bool), (fixture.chooseShape.secondParameter, .word)]
  wordInstantiation : wordShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation factoryWordRow.row
  boolInstantiation : boolShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation factoryBoolRow.row
  factoryWordInstantiation : factoryWordShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation chooseWordRow.row
  factoryBoolInstantiation : factoryBoolShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation chooseBoolRow.row
  noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []
  profile : fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true

def observeProgram (fixture : CompiledFixture) : IO (ObservedProgram fixture) := do
  let wordRow ← observeRootRow fixture fixture.wordSignature
  let boolRow ← observeRootRow fixture fixture.boolSignature
  let factoryWordRow ← observeRow fixture fixture.factorySignature [.word, .bool]
  let factoryBoolRow ← observeRow fixture fixture.factorySignature [.bool, .word]
  let chooseWordRow ← observeRow fixture fixture.chooseSignature [.word, .bool]
  let chooseBoolRow ← observeRow fixture fixture.chooseSignature [.bool, .word]
  let wordShape ← observeRoot wordRow.row.function fixture.wordSignature fixture.factorySignature fixture.factoryFirstParameter fixture.factorySecondParameter .word .bool fixture.trait
  let boolShape ← observeRoot boolRow.row.function fixture.boolSignature fixture.factorySignature fixture.factoryFirstParameter fixture.factorySecondParameter .bool .word fixture.trait
  let factoryWordShape ← observeFactory factoryWordRow.row.function fixture.factorySignature fixture.chooseSignature fixture.chooseShape.firstParameter fixture.chooseShape.secondParameter .word .bool fixture.trait
  let factoryBoolShape ← observeFactory factoryBoolRow.row.function fixture.factorySignature fixture.chooseSignature fixture.chooseShape.firstParameter fixture.chooseShape.secondParameter .bool .word fixture.trait
  let chooseWordShape ← observeSelected chooseWordRow.row.function .word .bool
  let chooseBoolShape ← observeSelected chooseBoolRow.row.function .bool .word
  let ⟨indexCoverage⟩ ← observed ((List.range 6).all (fun index => decide (index ∈ [wordRow.index, boolRow.index, factoryWordRow.index, factoryBoolRow.index, chooseWordRow.index, chooseBoolRow.index])) = true) "actual six slots coverage"
  let ⟨globalsLength⟩ ← observed (fixture.recipe.compiled.indexed.base.globals.length = 6) "evidence program globalsLength"
  let ⟨wordBool⟩ ← observed (wordRow.index ≠ boolRow.index) "evidence program wordBool"
  let ⟨wordFactoryWord⟩ ← observed (wordRow.index ≠ factoryWordRow.index) "evidence program wordFactoryWord"
  let ⟨wordFactoryBool⟩ ← observed (wordRow.index ≠ factoryBoolRow.index) "evidence program wordFactoryBool"
  let ⟨wordChooseWord⟩ ← observed (wordRow.index ≠ chooseWordRow.index) "evidence program wordChooseWord"
  let ⟨wordChooseBool⟩ ← observed (wordRow.index ≠ chooseBoolRow.index) "evidence program wordChooseBool"
  let ⟨boolFactoryWord⟩ ← observed (boolRow.index ≠ factoryWordRow.index) "evidence program boolFactoryWord"
  let ⟨boolFactoryBool⟩ ← observed (boolRow.index ≠ factoryBoolRow.index) "evidence program boolFactoryBool"
  let ⟨boolChooseWord⟩ ← observed (boolRow.index ≠ chooseWordRow.index) "evidence program boolChooseWord"
  let ⟨boolChooseBool⟩ ← observed (boolRow.index ≠ chooseBoolRow.index) "evidence program boolChooseBool"
  let ⟨factoryWordFactoryBool⟩ ← observed (factoryWordRow.index ≠ factoryBoolRow.index) "evidence program factoryWordFactoryBool"
  let ⟨factoryWordChooseWord⟩ ← observed (factoryWordRow.index ≠ chooseWordRow.index) "evidence program factoryWordChooseWord"
  let ⟨factoryWordChooseBool⟩ ← observed (factoryWordRow.index ≠ chooseBoolRow.index) "evidence program factoryWordChooseBool"
  let ⟨factoryBoolChooseWord⟩ ← observed (factoryBoolRow.index ≠ chooseWordRow.index) "evidence program factoryBoolChooseWord"
  let ⟨factoryBoolChooseBool⟩ ← observed (factoryBoolRow.index ≠ chooseBoolRow.index) "evidence program factoryBoolChooseBool"
  let ⟨chooseWordChooseBool⟩ ← observed (chooseWordRow.index ≠ chooseBoolRow.index) "evidence program chooseWordChooseBool"
  let ⟨wordNodes⟩ ← observed (wordRow.row.function.typedBody.nodes = wordShape.nodeList) "evidence program wordNodes"
  let ⟨boolNodes⟩ ← observed (boolRow.row.function.typedBody.nodes = boolShape.nodeList) "evidence program boolNodes"
  let ⟨factoryWordNodes⟩ ← observed (factoryWordRow.row.function.typedBody.nodes = factoryWordShape.nodeList) "evidence program factoryWordNodes"
  let ⟨factoryBoolNodes⟩ ← observed (factoryBoolRow.row.function.typedBody.nodes = factoryBoolShape.nodeList) "evidence program factoryBoolNodes"
  let ⟨chooseWordNodes⟩ ← observed (chooseWordRow.row.function.typedBody.nodes = chooseWordShape.nodeList) "evidence program chooseWordNodes"
  let ⟨chooseBoolNodes⟩ ← observed (chooseBoolRow.row.function.typedBody.nodes = chooseBoolShape.nodeList) "evidence program chooseBoolNodes"
  let ⟨wordResultType⟩ ← observed (wordRow.row.function.inferredBodyType = closureType .word) "evidence program wordResultType"
  let ⟨boolResultType⟩ ← observed (boolRow.row.function.inferredBodyType = closureType .bool) "evidence program boolResultType"
  let ⟨factoryWordResultType⟩ ← observed (factoryWordRow.row.function.inferredBodyType = closureType .word) "evidence program factoryWordResultType"
  let ⟨factoryBoolResultType⟩ ← observed (factoryBoolRow.row.function.inferredBodyType = closureType .bool) "evidence program factoryBoolResultType"
  let ⟨wordKey⟩ ← observed (wordRow.row.key = ⟨fixture.wordSignature.id, []⟩) "evidence program wordKey"
  let ⟨boolKey⟩ ← observed (boolRow.row.key = ⟨fixture.boolSignature.id, []⟩) "evidence program boolKey"
  let ⟨factoryWordKey⟩ ← observed (factoryWordRow.row.key = ⟨fixture.factorySignature.id, [.word, .bool]⟩) "evidence program factoryWordKey"
  let ⟨factoryBoolKey⟩ ← observed (factoryBoolRow.row.key = ⟨fixture.factorySignature.id, [.bool, .word]⟩) "evidence program factoryBoolKey"
  let ⟨chooseWordKey⟩ ← observed (chooseWordRow.row.key = ⟨fixture.chooseSignature.id, [.word, .bool]⟩) "evidence program chooseWordKey"
  let ⟨chooseBoolKey⟩ ← observed (chooseBoolRow.row.key = ⟨fixture.chooseSignature.id, [.bool, .word]⟩) "evidence program chooseBoolKey"
  let ⟨wordParameters⟩ ← observed (wordRow.row.parameterSubstitution = []) "evidence program wordParameters"
  let ⟨boolParameters⟩ ← observed (boolRow.row.parameterSubstitution = []) "evidence program boolParameters"
  let ⟨factoryWordParameters⟩ ← observed (factoryWordRow.row.parameterSubstitution = [(fixture.factoryFirstParameter, .word), (fixture.factorySecondParameter, .bool)]) "evidence program factoryWordParameters"
  let ⟨factoryBoolParameters⟩ ← observed (factoryBoolRow.row.parameterSubstitution = [(fixture.factoryFirstParameter, .bool), (fixture.factorySecondParameter, .word)]) "evidence program factoryBoolParameters"
  let ⟨chooseWordParameters⟩ ← observed (chooseWordRow.row.parameterSubstitution = [(fixture.chooseShape.firstParameter, .word), (fixture.chooseShape.secondParameter, .bool)]) "evidence program chooseWordParameters"
  let ⟨chooseBoolParameters⟩ ← observed (chooseBoolRow.row.parameterSubstitution = [(fixture.chooseShape.firstParameter, .bool), (fixture.chooseShape.secondParameter, .word)]) "evidence program chooseBoolParameters"
  let ⟨wordInstantiation⟩ ← observed (wordShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation factoryWordRow.row) "evidence program wordInstantiation"
  let ⟨boolInstantiation⟩ ← observed (boolShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation factoryBoolRow.row) "evidence program boolInstantiation"
  let ⟨factoryWordInstantiation⟩ ← observed (factoryWordShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation chooseWordRow.row) "evidence program factoryWordInstantiation"
  let ⟨factoryBoolInstantiation⟩ ← observed (factoryBoolShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation chooseBoolRow.row) "evidence program factoryBoolInstantiation"
  let ⟨noLocals⟩ ← observed (fixture.recipe.compiled.indexed.base.locals.bindings = []) "evidence program noLocals"
  let ⟨profile⟩ ← observed (fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true) "evidence program profile"
  return {indexCoverage, wordRow, boolRow, factoryWordRow, factoryBoolRow, chooseWordRow, chooseBoolRow, globalsLength, wordBool, wordFactoryWord, wordFactoryBool, wordChooseWord, wordChooseBool, boolFactoryWord, boolFactoryBool, boolChooseWord, boolChooseBool, factoryWordFactoryBool, factoryWordChooseWord, factoryWordChooseBool, factoryBoolChooseWord, factoryBoolChooseBool, chooseWordChooseBool, wordShape, boolShape, factoryWordShape, factoryBoolShape, chooseWordShape, chooseBoolShape, wordNodes, boolNodes, factoryWordNodes, factoryBoolNodes, chooseWordNodes, chooseBoolNodes, wordResultType, boolResultType, factoryWordResultType, factoryBoolResultType, wordKey, boolKey, factoryWordKey, factoryBoolKey, chooseWordKey, chooseBoolKey, wordParameters, boolParameters, factoryWordParameters, factoryBoolParameters, chooseWordParameters, chooseBoolParameters, wordInstantiation, boolInstantiation, factoryWordInstantiation, factoryBoolInstantiation, noLocals, profile}

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

theorem ObservedRow.issue {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    (observed : ObservedRow fixture signature) :
    ∃ input : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled,
      input.row = observed.row ∧
      ∃ packet : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued input,
      ∃ actual : ActualHeader fixture observed.row,
        actual.header = packet.header ∧ actual.header.slot = observed.index ∧ actual.header.named.signature = observed.global := by
  obtain ⟨prepared⟩ := fixture.prepared observed.member
  obtain ⟨signatureEq, indexEq⟩ := observed.prepared_slot prepared
  have range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures fixture.recipe.compiled.sourceProgram.signatures) observed.row.parameterSubstitution := by
    intro parameter replacement member
    have scalar := of_decide_eq_true (List.all_eq_true.mp observed.scalarRange (parameter, replacement) member)
    rcases scalar with rfl | rfl
    · exact ⟨by simp [TypeParameterBindersWellFormed, Context.ofSignatures], .builtin .word⟩
    · exact ⟨by simp [TypeParameterBindersWellFormed, Context.ofSignatures], .builtin .bool⟩
  let input : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled := {
    row := observed.row
    prepared := prepared
    range := range
    ordinaryReturn := observed.ordinary
    ordinaryParameters := observed.inputsOrdinary
    target := by rw [RecursiveNamedPreparedCallEvidence.Prepared.signature_key prepared]; exact observed.target
    slot := by rw [signatureEq, indexEq]; exact observed.slot }
  obtain ⟨packet⟩ := CallableIndexedOwnedPreparedFiniteNamedInventories.issue fixture.source_wellFormed input
  let actual : ActualHeader fixture observed.row := {
    prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued prepared packet.selected
    header := packet.header
    aligned := packet.aligned
    diagnostic := ⟨⟨packet.selected.diagnostics, packet.selected.found, rfl⟩⟩ }
  exact ⟨input, rfl, packet, actual, rfl, actual.aligned.slot.trans indexEq,
    (congrArg (·.signature) actual.aligned.named).trans signatureEq⟩

theorem ObservedProgram.inventory {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    ∃ (wordInput boolInput factoryWordInput factoryBoolInput chooseWordInput chooseBoolInput : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled),
      wordInput.row = observed.wordRow.row ∧ boolInput.row = observed.boolRow.row ∧ factoryWordInput.row = observed.factoryWordRow.row ∧ factoryBoolInput.row = observed.factoryBoolRow.row ∧ chooseWordInput.row = observed.chooseWordRow.row ∧ chooseBoolInput.row = observed.chooseBoolRow.row ∧
      ∃ (wordPacket : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued wordInput)
        (boolPacket : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued boolInput)
        (factoryWordPacket : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued factoryWordInput)
        (factoryBoolPacket : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued factoryBoolInput)
        (chooseWordPacket : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued chooseWordInput)
        (chooseBoolPacket : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued chooseBoolInput),
      ∃ (wordHeader : ActualHeader fixture observed.wordRow.row)
        (boolHeader : ActualHeader fixture observed.boolRow.row)
        (factoryWordHeader : ActualHeader fixture observed.factoryWordRow.row)
        (factoryBoolHeader : ActualHeader fixture observed.factoryBoolRow.row)
        (chooseWordHeader : ActualHeader fixture observed.chooseWordRow.row)
        (chooseBoolHeader : ActualHeader fixture observed.chooseBoolRow.row),
        wordHeader.header = wordPacket.header ∧ boolHeader.header = boolPacket.header ∧ factoryWordHeader.header = factoryWordPacket.header ∧ factoryBoolHeader.header = factoryBoolPacket.header ∧ chooseWordHeader.header = chooseWordPacket.header ∧ chooseBoolHeader.header = chooseBoolPacket.header ∧
        RecursiveNamedCatalogNativeContexts.Complete
          (values := .initial fixture.recipe.compiled.compatible.checked)
          (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
          (CallableIndexedOwnedPreparedFiniteNamedInventories.headers (.cons wordPacket (.cons boolPacket (.cons factoryWordPacket (.cons factoryBoolPacket (.cons chooseWordPacket (.cons chooseBoolPacket .nil))))))) := by
  obtain ⟨wordInput, wordRow, wordPacket, wordHeader, wordEq, wordSlot, wordSignature⟩ := observed.wordRow.issue
  obtain ⟨boolInput, boolRow, boolPacket, boolHeader, boolEq, boolSlot, boolSignature⟩ := observed.boolRow.issue
  obtain ⟨factoryWordInput, factoryWordRow, factoryWordPacket, factoryWordHeader, factoryWordEq, factoryWordSlot, factoryWordSignature⟩ := observed.factoryWordRow.issue
  obtain ⟨factoryBoolInput, factoryBoolRow, factoryBoolPacket, factoryBoolHeader, factoryBoolEq, factoryBoolSlot, factoryBoolSignature⟩ := observed.factoryBoolRow.issue
  obtain ⟨chooseWordInput, chooseWordRow, chooseWordPacket, chooseWordHeader, chooseWordEq, chooseWordSlot, chooseWordSignature⟩ := observed.chooseWordRow.issue
  obtain ⟨chooseBoolInput, chooseBoolRow, chooseBoolPacket, chooseBoolHeader, chooseBoolEq, chooseBoolSlot, chooseBoolSignature⟩ := observed.chooseBoolRow.issue
  refine ⟨wordInput, boolInput, factoryWordInput, factoryBoolInput, chooseWordInput, chooseBoolInput, wordRow, boolRow, factoryWordRow, factoryBoolRow, chooseWordRow, chooseBoolRow, wordPacket, boolPacket, factoryWordPacket, factoryBoolPacket, chooseWordPacket, chooseBoolPacket, wordHeader, boolHeader, factoryWordHeader, factoryBoolHeader, chooseWordHeader, chooseBoolHeader, wordEq, boolEq, factoryWordEq, factoryBoolEq, chooseWordEq, chooseBoolEq, ?_⟩
  intro index signature found
  have bound := (List.getElem?_eq_some_iff.mp found).1
  rw [observed.globalsLength] at bound
  have casesIndex : index = observed.wordRow.index ∨ index = observed.boolRow.index ∨ index = observed.factoryWordRow.index ∨ index = observed.factoryBoolRow.index ∨ index = observed.chooseWordRow.index ∨ index = observed.chooseBoolRow.index := by
    have contained := of_decide_eq_true (List.all_eq_true.mp observed.indexCoverage index (List.mem_range.mpr bound))
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using contained
  rcases casesIndex with same | same | same | same | same | same
  · refine ⟨wordHeader.header, ?_, wordSlot.trans same.symm, ?_⟩
    · rw [wordEq]; exact .head _
    · rw [same, observed.wordRow.slot.selected] at found
      exact wordSignature.trans (Option.some.inj found)
  · refine ⟨boolHeader.header, ?_, boolSlot.trans same.symm, ?_⟩
    · rw [boolEq]; exact .tail _ (.head _)
    · rw [same, observed.boolRow.slot.selected] at found
      exact boolSignature.trans (Option.some.inj found)
  · refine ⟨factoryWordHeader.header, ?_, factoryWordSlot.trans same.symm, ?_⟩
    · rw [factoryWordEq]; exact .tail _ (.tail _ (.head _))
    · rw [same, observed.factoryWordRow.slot.selected] at found
      exact factoryWordSignature.trans (Option.some.inj found)
  · refine ⟨factoryBoolHeader.header, ?_, factoryBoolSlot.trans same.symm, ?_⟩
    · rw [factoryBoolEq]; exact .tail _ (.tail _ (.tail _ (.head _)))
    · rw [same, observed.factoryBoolRow.slot.selected] at found
      exact factoryBoolSignature.trans (Option.some.inj found)
  · refine ⟨chooseWordHeader.header, ?_, chooseWordSlot.trans same.symm, ?_⟩
    · rw [chooseWordEq]; exact .tail _ (.tail _ (.tail _ (.tail _ (.head _))))
    · rw [same, observed.chooseWordRow.slot.selected] at found
      exact chooseWordSignature.trans (Option.some.inj found)
  · refine ⟨chooseBoolHeader.header, ?_, chooseBoolSlot.trans same.symm, ?_⟩
    · rw [chooseBoolEq]; exact .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
    · rw [same, observed.chooseBoolRow.slot.selected] at found
      exact chooseBoolSignature.trans (Option.some.inj found)
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

def seed : Core.Word := Core.Word.ofNatModulo 11

def runOptions : SourceCoreExecution.RunOptions := {
  executionFuel := 100000
  inputValidationFuel := 1000
  outputValidationFuel := 1000 }

/-- Concrete public execution retains the original opened artifact, fresh
bootstrap and exact run receipt. Its scalar output is obtained from the actual public execution. -/
structure ObservedPublicRun (fixture : CompiledFixture) {signature : ProgramFunctionSignature} (observed : ObservedRow fixture signature) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facadeCompiled
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start observed.row.key [.word seed, .bool true] runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion artifact
  executed : session.RunAt observed.row.key [.word seed, .bool true] runOptions (.ok (.succeeded completion))
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
    match started : session.start observed.row.key [.word seed, .bool true] runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint =>
      let executed ← session.runWithReceipt observed.row.key [.word seed, .bool true] runOptions
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
        | _ => throw (IO.userError "factory expected closure export")


end Tests.SourceCoreEvidenceClosure
end

section
-- leanmerge: from Solcore.Test.SourceCoreEvidenceClosureLeafSupport
/-! Both selected generic bodies are genuine specialized reads. Their metadata
and terminal support come from the actual source graph and compiler receipt. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreEvidenceClosure
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

section Selected
variable {fixture : CompiledFixture} {row : SourceSpecialization.SpecializedFunction}
    {firstType secondType : TypeSystem.Ty}
    (shape : SelectedShape row.function firstType secondType)
    (nodes : row.function.typedBody.nodes = shape.nodeList)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = [])
    (actual : ActualHeader fixture row)

include nodes in
private theorem selected_expression {id : ExpressionId} {node : ExpressionNode}
    (found : row.function.typedBody.lookupExpression? id = some node) : node = shape.read.node := by
  have present := (lookupExpression?_sound found).1
  rw [nodes] at present
  simpa only [SelectedShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present

include nodes noLocals in
theorem ActualHeader.selected_metadata (named : CallableIndexedNamedGeneration.Named) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.MetadataFor
      fixture.recipe.compiled.indexed named actual.header.function.source := by
  constructor
  · intro id _ node found
    rw [actual.source] at found
    rw [selected_expression shape nodes found]
    exact shape.read.requirements
  · intro id _ node found
    rw [actual.source] at found
    rw [selected_expression shape nodes found]
    exact shape.read.coercions
  · intro id _
    simp only [noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    rw [actual.source] at found
    rw [selected_expression shape nodes found, shape.read.form] at form
    cases form
  · intro id _ node _found name binder _form
    simp only [noLocals, List.any_nil]

theorem ActualHeader.selected_syntax :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax
      actual.header.function.source shape.read.node.id := by
  rw [actual.source]
  exact .leaf (.read shape.read.found shape.read.form)

include nodes noLocals in
theorem ActualHeader.selected_support
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    ∃ terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header,
      terminal.expression = shape.read.node.id ∧
      Nonempty (CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.NamedSupport
        actual.header (RecursiveNamedPreparedStageScopes.registry stagePrepared) terminal
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  obtain ⟨terminal, diagnostic, expression, point⟩ := actual.terminal shape.read.node.id
    shape.statement shape.roots shape.statementFound shape.statementForm
  exact ⟨terminal, expression, CallableIndexedOwnedPreparedStagedNamedRecursiveTerminalSupport.of_actual
    terminal diagnostic receiver fixture.source_wellFormed
    (ActualHeader.selected_metadata shape nodes noLocals actual terminal.prepared.named)
    (by rw [expression]; exact ActualHeader.selected_syntax shape actual) stagePrepared point⟩
end Selected

theorem ActualHeader.chooseWord_support {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.chooseWordRow.row)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    ∃ terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header,
      terminal.expression = observed.chooseWordShape.read.node.id ∧
      Nonempty (CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.NamedSupport
        actual.header (RecursiveNamedPreparedStageScopes.registry stagePrepared) terminal
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  exact ActualHeader.selected_support observed.chooseWordShape observed.chooseWordNodes observed.noLocals actual receiver stagePrepared

theorem ActualHeader.chooseBool_support {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.chooseBoolRow.row)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    ∃ terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header,
      terminal.expression = observed.chooseBoolShape.read.node.id ∧
      Nonempty (CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.NamedSupport
        actual.header (RecursiveNamedPreparedStageScopes.registry stagePrepared) terminal
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  exact ActualHeader.selected_support observed.chooseBoolShape observed.chooseBoolNodes observed.noLocals actual receiver stagePrepared

end Tests.SourceCoreEvidenceClosure
end

section
-- leanmerge: from Solcore.Test.SourceCoreEvidenceClosureMetadata
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreEvidenceClosure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (SupportedSyntax)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Supported)

theorem ObservedRow.record {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    (row : ObservedRow fixture signature) :
    SourceCompilationPlan.exactSpecialization fixture.recipe.compiled.indexed.base.plan row.row.key = .ok row.row := by
  obtain ⟨input, _same, packet, actual, _⟩ := row.issue
  have record := CallableIndexedActualNamedSourceReceipts.header_record fixture.recipe.compiled actual.header
  rw [actual.aligned.named, RecursiveNamedPreparedCallEvidence.Prepared.signature_key actual.prepared,
    actual.prepared.same] at record
  exact record

private theorem retained_ordered {plan : SourceCompilationPlan.Plan}
    {row : SourceSpecialization.SpecializedFunction}
    (target : SourceCompilationPlan.exactInstantiationKey plan
      (CallableNamedCanonicalOrder.retainedInstantiation row) = .ok row.key)
    (record : SourceCompilationPlan.exactSpecialization plan row.key = .ok row) :
    RecursiveNamedCallSelectionCertificates.Ordered plan
      (CallableNamedCanonicalOrder.retainedInstantiation row) := by
  intro key selected selectedTarget selectedRecord
  have sameKey := Except.ok.inj (target.symm.trans selectedTarget)
  subst key
  have sameRow := Except.ok.inj (record.symm.trans selectedRecord)
  subst selected
  exact List.map_reverse

theorem ObservedProgram.word_supported {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) :
    Supported fixture.recipe.compiled.indexed.base.plan observed.wordShape.call.instantiation := by
  refine ⟨?_, ?_⟩
  · intro parameter replacement member
    rw [observed.wordShape.call.exact] at member
    rcases List.mem_cons.mp member with same | member
    · rw [(Prod.mk.inj same).2]; rfl
    · have same := List.mem_singleton.mp member
      rw [(Prod.mk.inj same).2]; rfl
  · rw [observed.wordInstantiation]
    exact retained_ordered observed.factoryWordRow.target observed.factoryWordRow.record

theorem ObservedProgram.bool_supported {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) :
    Supported fixture.recipe.compiled.indexed.base.plan observed.boolShape.call.instantiation := by
  refine ⟨?_, ?_⟩
  · intro parameter replacement member
    rw [observed.boolShape.call.exact] at member
    rcases List.mem_cons.mp member with same | member
    · rw [(Prod.mk.inj same).2]; rfl
    · have same := List.mem_singleton.mp member
      rw [(Prod.mk.inj same).2]; rfl
  · rw [observed.boolInstantiation]
    exact retained_ordered observed.factoryBoolRow.target observed.factoryBoolRow.record

theorem ObservedProgram.factoryWord_supported {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) :
    Supported fixture.recipe.compiled.indexed.base.plan observed.factoryWordShape.call.instantiation := by
  refine ⟨?_, ?_⟩
  · intro parameter replacement member
    rw [observed.factoryWordShape.call.exact] at member
    rcases List.mem_cons.mp member with same | member
    · rw [(Prod.mk.inj same).2]; rfl
    · have same := List.mem_singleton.mp member
      rw [(Prod.mk.inj same).2]; rfl
  · rw [observed.factoryWordInstantiation]
    exact retained_ordered observed.chooseWordRow.target observed.chooseWordRow.record

theorem ObservedProgram.factoryBool_supported {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) :
    Supported fixture.recipe.compiled.indexed.base.plan observed.factoryBoolShape.call.instantiation := by
  refine ⟨?_, ?_⟩
  · intro parameter replacement member
    rw [observed.factoryBoolShape.call.exact] at member
    rcases List.mem_cons.mp member with same | member
    · rw [(Prod.mk.inj same).2]; rfl
    · have same := List.mem_singleton.mp member
      rw [(Prod.mk.inj same).2]; rfl
  · rw [observed.factoryBoolInstantiation]
    exact retained_ordered observed.chooseBoolRow.target observed.chooseBoolRow.record

section Root
variable {function : CheckedFunction} {signature generic : ProgramFunctionSignature}
  {firstParameter secondParameter : TypeSystem.TypeParameterId} {firstType secondType : TypeSystem.Ty} {trait : ProgramTraitId}
  (shape : RootShape function signature generic firstParameter secondParameter firstType secondType trait)
  (nodes : function.typedBody.nodes = shape.nodeList)

include nodes in
theorem RootShape.expressions {id : ExpressionId} {node : ExpressionNode}
    (found : function.typedBody.lookupExpression? id = some node) :
    node = shape.firstRead.node ∨ node = shape.secondRead.node ∨
      node = shape.call.callee.node ∨ node = shape.call.value.node := by
  have present := (lookupExpression?_sound found).1
  rw [nodes] at present
  simpa only [RootShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present

include nodes in
theorem RootShape.metadata {fixture : CompiledFixture}
    (named : CallableIndexedNamedGeneration.Named)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []) :
    CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles.MetadataFor
      fixture.recipe.compiled.indexed named function.typedBody
      (Supported fixture.recipe.compiled.indexed.base.plan) := by
  constructor
  · intro id _ node found
    rcases shape.expressions nodes found with same | same | same | same
    all_goals subst node
    · exact .inl shape.firstRead.requirements
    · exact .inl shape.secondRead.requirements
    · exact .inl shape.call.callee.requirements
    · exact .inr (.inr ⟨_, _, _, shape.call.form⟩)
  · intro id _ node found
    rcases shape.expressions nodes found with same | same | same | same
    all_goals subst node
    · exact shape.firstRead.coercions
    · exact shape.secondRead.coercions
    · exact shape.call.callee.coercions
    · exact shape.call.value.coercions
  · intro id _
    simp only [noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    rcases shape.expressions nodes found with same | same | same | same
    all_goals subst node
    · rw [shape.firstRead.form] at form; cases form
    · rw [shape.secondRead.form] at form; cases form
    · rw [shape.call.calleeForm] at form; cases form
    · rw [shape.call.form] at form; cases form
  · intro id _ node _found name binder _form
    simp only [noLocals, List.any_nil]

theorem RootShape.syntax {plan : SourceCompilationPlan.Plan}
    (ordinary : Supported plan shape.call.instantiation) :
    SupportedSyntax plan function.typedBody shape.call.value.node.id := by
  refine .direct shape.call.value.found shape.call.form ordinary ?_
  intro id member
  rcases List.mem_cons.mp member with same | member
  · subst id
    exact .leaf (.read shape.firstRead.found shape.firstRead.form)
  · have same := List.mem_singleton.mp member
    subst id
    exact .leaf (.read shape.secondRead.found shape.secondRead.form)
end Root
section Factory
variable {function : CheckedFunction} {signature generic : ProgramFunctionSignature}
  {firstParameter secondParameter : TypeSystem.TypeParameterId} {firstType secondType : TypeSystem.Ty} {trait : ProgramTraitId}
  (shape : FactoryShape function signature generic firstParameter secondParameter firstType secondType trait)
  (nodes : function.typedBody.nodes = shape.nodeList)

include nodes in
theorem FactoryShape.expressions {id : ExpressionId} {node : ExpressionNode}
    (found : function.typedBody.lookupExpression? id = some node) :
    node = shape.firstRead.node ∨ node = shape.secondRead.node ∨
      node = shape.call.callee.node ∨ node = shape.call.value.node ∨ node = shape.expression := by
  have present := (lookupExpression?_sound found).1
  rw [nodes] at present
  simpa only [FactoryShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present

include nodes in
theorem FactoryShape.metadata {fixture : CompiledFixture}
    (named : CallableIndexedNamedGeneration.Named)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []) :
    CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles.MetadataFor
      fixture.recipe.compiled.indexed named function.typedBody
      (Supported fixture.recipe.compiled.indexed.base.plan) := by
  constructor
  · intro id _ node found
    rcases shape.expressions nodes found with same | same | same | same | same
    all_goals subst node
    · exact .inl shape.firstRead.requirements
    · exact .inl shape.secondRead.requirements
    · exact .inl shape.call.callee.requirements
    · exact .inr (.inr ⟨_, _, _, shape.call.form⟩)
    · exact .inl shape.requirements
  · intro id _ node found
    rcases shape.expressions nodes found with same | same | same | same | same
    all_goals subst node
    · exact shape.firstRead.coercions
    · exact shape.secondRead.coercions
    · exact shape.call.callee.coercions
    · exact shape.call.value.coercions
    · exact shape.coercions
  · intro id _
    simp only [noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    rcases shape.expressions nodes found with same | same | same | same | same
    all_goals subst node
    · rw [shape.firstRead.form] at form; cases form
    · rw [shape.secondRead.form] at form; cases form
    · rw [shape.call.calleeForm] at form; cases form
    · rw [shape.call.form] at form; cases form
    · rw [shape.lambda] at form; cases form
  · intro id _ node _found name binder _form
    simp only [noLocals, List.any_nil]

theorem FactoryShape.syntax {plan : SourceCompilationPlan.Plan}
    (ordinary : Supported plan shape.call.instantiation) :
    SupportedSyntax plan function.typedBody shape.call.value.node.id := by
  refine .direct shape.call.value.found shape.call.form ordinary ?_
  intro id member
  rcases List.mem_cons.mp member with same | member
  · subst id
    exact .leaf (.read shape.firstRead.found shape.firstRead.form)
  · have same := List.mem_singleton.mp member
    subst id
    exact .leaf (.read shape.secondRead.found shape.secondRead.form)
end Factory
end Tests.SourceCoreEvidenceClosure
end

section
-- leanmerge: from Solcore.Test.SourceCoreEvidenceClosureRootSupport
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreEvidenceClosure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Supported)

/-- The original nonempty instantiation remains attached to the actual
terminal callback and the complete inventory that issued its selected callee. -/
theorem ActualHeader.root_support {fixture : CompiledFixture}
    {signature generic : ProgramFunctionSignature}
    {firstParameter secondParameter : TypeSystem.TypeParameterId}
    {firstType secondType : TypeSystem.Ty} {trait : ProgramTraitId}
    (row : ObservedRow fixture signature)
    (shape : RootShape row.row.function signature generic firstParameter secondParameter firstType secondType trait)
    (nodes : row.row.function.typedBody.nodes = shape.nodeList)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = [])
    (ordinary : Supported fixture.recipe.compiled.indexed.base.plan shape.call.instantiation)
    (actual : ActualHeader fixture row.row)
    {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled)}
    (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows))
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    ∃ terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header,
      terminal.expression = shape.call.value.node.id ∧
      Nonempty (CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.NamedSupport
        (headers := CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
        (keys := CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        (RecursiveNamedPreparedStageScopes.registry stagePrepared)
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
        actual.header terminal) := by
  obtain ⟨terminal, diagnostic, expression, point⟩ := actual.terminal shape.call.value.node.id
    shape.statement shape.roots shape.statementFound shape.statementForm
  have metadata : CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles.MetadataFor
      fixture.recipe.compiled.indexed terminal.prepared.named actual.header.function.source
      (Supported fixture.recipe.compiled.indexed.base.plan) := by
    rw [actual.source]
    exact shape.metadata nodes terminal.prepared.named noLocals
  exact ⟨terminal, expression,
    CallableIndexedOwnedPreparedStagedNamedEvidenceTerminalSupport.of_actual
      terminal diagnostic receiver fixture.source_wellFormed (fun _ witness => witness) metadata
      (by rw [expression, actual.source]; exact shape.syntax ordinary)
      rows complete (bootstrap_zero fixture.recipe.compiled) stagePrepared point⟩

theorem ActualHeader.word_support {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.wordRow.row)
    {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled)}
    (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows))
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    ∃ terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header,
      terminal.expression = observed.wordShape.call.value.node.id ∧
      Nonempty (CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.NamedSupport
        (headers := CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
        (keys := CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        (RecursiveNamedPreparedStageScopes.registry stagePrepared)
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
        actual.header terminal) :=
  actual.root_support observed.wordRow.toObservedRow observed.wordShape observed.wordNodes
    observed.noLocals observed.word_supported rows complete receiver stagePrepared

theorem ActualHeader.bool_support {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.boolRow.row)
    {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled)}
    (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows))
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    ∃ terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header,
      terminal.expression = observed.boolShape.call.value.node.id ∧
      Nonempty (CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.NamedSupport
        (headers := CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
        (keys := CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        (RecursiveNamedPreparedStageScopes.registry stagePrepared)
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
        actual.header terminal) :=
  actual.root_support observed.boolRow.toObservedRow observed.boolShape observed.boolNodes
    observed.noLocals observed.bool_supported rows complete receiver stagePrepared


end Tests.SourceCoreEvidenceClosure
end

section
-- leanmerge: from Solcore.Test.SourceCoreEvidenceClosureRuntime
/-! Actual public calls reuse distinct closure exports through the returned
sessions. Every step retains its original startup and run receipts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreEvidenceClosure
open Solcore Frontend SourceInference SourceSemantics

def secondSeed : Core.Word := Core.Word.ofNatModulo 20

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

structure ObservedInvocation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle)
    (argument : SourceCorePublicValues.Value) where
  completion : SourceCoreExecution.Completion artifact
  executed : session.InvokeAt handle argument runOptions (.ok (.succeeded completion))

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


structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  first : ObservedPublicRun fixture observed.wordRow.toObservedRow
  second : ObservedFunctionCall first.completion.session observed.boolRow.row.key
    [.bool false, .word (Core.Word.ofNatModulo 22)]
  firstRead : ObservedInvocation second.completion.session first.handle .unit
  firstValue : firstRead.completion.value = .word seed
  third : ObservedFunctionCall firstRead.completion.session observed.wordRow.row.key
    [.word (Core.Word.ofNatModulo 33), .bool false]
  firstSecond : first.handle ≠ second.handle
  firstThird : first.handle ≠ third.handle
  secondThird : second.handle ≠ third.handle
  secondRead : ObservedInvocation third.completion.session second.handle .unit
  secondValue : secondRead.completion.value = .bool false
  repeatedRead : ObservedInvocation secondRead.completion.session first.handle .unit
  repeatedValue : repeatedRead.completion.value = .word seed
  thirdRead : ObservedInvocation repeatedRead.completion.session third.handle .unit
  thirdValue : thirdRead.completion.value = .word (Core.Word.ofNatModulo 33)

def observeSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedSequence fixture observed) := do
  let first ← observePublicRun fixture observed.wordRow.toObservedRow
  let second ← observeFunctionCall first.completion.session observed.boolRow.row.key
    [.bool false, .word (Core.Word.ofNatModulo 22)]
  let firstRead ← observeInvocation second.completion.session first.handle .unit
  if firstValue : firstRead.completion.value = .word seed then
    let third ← observeFunctionCall firstRead.completion.session observed.wordRow.row.key
      [.word (Core.Word.ofNatModulo 33), .bool false]
    if firstSecond : first.handle ≠ second.handle then
      if firstThird : first.handle ≠ third.handle then
        if secondThird : second.handle ≠ third.handle then
          let secondRead ← observeInvocation third.completion.session second.handle .unit
          if secondValue : secondRead.completion.value = .bool false then
            let repeatedRead ← observeInvocation secondRead.completion.session first.handle .unit
            if repeatedValue : repeatedRead.completion.value = .word seed then
              let thirdRead ← observeInvocation repeatedRead.completion.session third.handle .unit
              if thirdValue : thirdRead.completion.value = .word (Core.Word.ofNatModulo 33) then
                return {
                  first := first
                  second := second
                  firstRead := firstRead
                  firstValue := firstValue
                  third := third
                  firstSecond := firstSecond
                  firstThird := firstThird
                  secondThird := secondThird
                  secondRead := secondRead
                  secondValue := secondValue
                  repeatedRead := repeatedRead
                  repeatedValue := repeatedValue
                  thirdRead := thirdRead
                  thirdValue := thirdValue
                }
              else throw (IO.userError "third Word closure capture changed")
            else throw (IO.userError "first Word closure capture changed on reuse")
          else throw (IO.userError "Bool closure capture changed")
        else throw (IO.userError "second and third exports alias")
      else throw (IO.userError "first and third exports alias")
    else throw (IO.userError "first and second exports alias")
  else throw (IO.userError "first Word closure capture changed")
end Tests.SourceCoreEvidenceClosure
end

section
-- leanmerge: from Solcore.Test.SourceCoreEvidenceClosureSelection
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreEvidenceClosure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicRootMeaning (RootSelection)
open RecursiveNamedPublicHistoryFrontdoor (Started)

theorem ActualHeader.key {fixture : CompiledFixture}
    {row : SourceSpecialization.SpecializedFunction} (actual : ActualHeader fixture row) :
    actual.header.named.signature.key = row.key := by
  rw [actual.aligned.named]
  exact RecursiveNamedPreparedCallEvidence.Prepared.signature_key actual.prepared

theorem ObservedRow.keys_ne {fixture : CompiledFixture} {leftSignature rightSignature : ProgramFunctionSignature}
    (left : ObservedRow fixture leftSignature) (right : ObservedRow fixture rightSignature)
    (distinct : left.index ≠ right.index) : left.row.key ≠ right.row.key := by
  intro same
  have globals : left.global.key = right.global.key := left.globalKey.trans (same.trans right.globalKey.symm)
  exact distinct (left.slot.unique right.slot globals).2

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

theorem selected_word_root {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordHeader : ActualHeader fixture observed.wordRow.row)
    (boolHeader : ActualHeader fixture observed.boolRow.row)
    (factoryWordHeader : ActualHeader fixture observed.factoryWordRow.row)
    (factoryBoolHeader : ActualHeader fixture observed.factoryBoolRow.row)
    (chooseWordHeader : ActualHeader fixture observed.chooseWordRow.row)
    (chooseBoolHeader : ActualHeader fixture observed.chooseBoolRow.row)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (selected : RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [wordHeader.header, boolHeader.header, factoryWordHeader.header, factoryBoolHeader.header, chooseWordHeader.header, chooseBoolHeader.header] root header)
    (key : root.key = observed.wordRow.row.key) : header = wordHeader.header := by
  have member : header ∈ [wordHeader.header, boolHeader.header, factoryWordHeader.header, factoryBoolHeader.header, chooseWordHeader.header, chooseBoolHeader.header] := selected.member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same | same | same | same
  · exact same
  · have headerKey := (selected_key selected).trans key
    rw [same, boolHeader.key] at headerKey
    exact False.elim ((observed.wordRow.keys_ne observed.boolRow.toObservedRow observed.wordBool) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, factoryWordHeader.key] at headerKey
    exact False.elim ((observed.wordRow.keys_ne observed.factoryWordRow observed.wordFactoryWord) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, factoryBoolHeader.key] at headerKey
    exact False.elim ((observed.wordRow.keys_ne observed.factoryBoolRow observed.wordFactoryBool) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, chooseWordHeader.key] at headerKey
    exact False.elim ((observed.wordRow.keys_ne observed.chooseWordRow observed.wordChooseWord) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, chooseBoolHeader.key] at headerKey
    exact False.elim ((observed.wordRow.keys_ne observed.chooseBoolRow observed.wordChooseBool) headerKey.symm)

theorem selected_bool_root {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordHeader : ActualHeader fixture observed.wordRow.row)
    (boolHeader : ActualHeader fixture observed.boolRow.row)
    (factoryWordHeader : ActualHeader fixture observed.factoryWordRow.row)
    (factoryBoolHeader : ActualHeader fixture observed.factoryBoolRow.row)
    (chooseWordHeader : ActualHeader fixture observed.chooseWordRow.row)
    (chooseBoolHeader : ActualHeader fixture observed.chooseBoolRow.row)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (selected : RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [wordHeader.header, boolHeader.header, factoryWordHeader.header, factoryBoolHeader.header, chooseWordHeader.header, chooseBoolHeader.header] root header)
    (key : root.key = observed.boolRow.row.key) : header = boolHeader.header := by
  have member : header ∈ [wordHeader.header, boolHeader.header, factoryWordHeader.header, factoryBoolHeader.header, chooseWordHeader.header, chooseBoolHeader.header] := selected.member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same | same | same | same
  · have headerKey := (selected_key selected).trans key
    rw [same, wordHeader.key] at headerKey
    exact False.elim ((observed.wordRow.keys_ne observed.boolRow.toObservedRow observed.wordBool) headerKey)
  · exact same
  · have headerKey := (selected_key selected).trans key
    rw [same, factoryWordHeader.key] at headerKey
    exact False.elim ((observed.boolRow.keys_ne observed.factoryWordRow observed.boolFactoryWord) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, factoryBoolHeader.key] at headerKey
    exact False.elim ((observed.boolRow.keys_ne observed.factoryBoolRow observed.boolFactoryBool) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, chooseWordHeader.key] at headerKey
    exact False.elim ((observed.boolRow.keys_ne observed.chooseWordRow observed.boolChooseWord) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, chooseBoolHeader.key] at headerKey
    exact False.elim ((observed.boolRow.keys_ne observed.chooseBoolRow observed.boolChooseBool) headerKey.symm)

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
    (wordHeader : ActualHeader fixture observed.wordRow.row)
    (boolHeader : ActualHeader fixture observed.boolRow.row)
    (factoryWordHeader : ActualHeader fixture observed.factoryWordRow.row)
    (factoryBoolHeader : ActualHeader fixture observed.factoryBoolRow.row)
    (chooseWordHeader : ActualHeader fixture observed.chooseWordRow.row)
    (chooseBoolHeader : ActualHeader fixture observed.chooseBoolRow.row)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {nativeArtifact : SourceCoreIndexedSession.Artifact}
    {session : SourceCoreIndexedSession.Session nativeArtifact}
    {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {world : Core.StoreTyping} {store : Core.Store}

theorem selected_word_at
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (headerList : headers = [wordHeader.header, boolHeader.header, factoryWordHeader.header, factoryBoolHeader.header, chooseWordHeader.header, chooseBoolHeader.header])
    (request : Started headers fixture.recipePrepared publicCheckpoint session
      observed.wordRow.row.key arguments fuel world store) : request.header = wordHeader.header := by
  subst headers
  exact selected_word_root wordHeader boolHeader factoryWordHeader factoryBoolHeader chooseWordHeader chooseBoolHeader request.selected (started_key request)

theorem selected_bool_at
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (headerList : headers = [wordHeader.header, boolHeader.header, factoryWordHeader.header, factoryBoolHeader.header, chooseWordHeader.header, chooseBoolHeader.header])
    (request : Started headers fixture.recipePrepared publicCheckpoint session
      observed.boolRow.row.key arguments fuel world store) : request.header = boolHeader.header := by
  subst headers
  exact selected_bool_root wordHeader boolHeader factoryWordHeader factoryBoolHeader chooseWordHeader chooseBoolHeader request.selected (started_key request)
end StartedSelection

theorem ActualHeader.word_input_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.wordRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.word, .bool] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.wordShape.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    observed.wordShape.firstScheme, observed.wordShape.secondScheme, TypeSystem.Scheme.mono] using inputs.symm

theorem ActualHeader.word_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.wordRow.row) : actual.header.types = [.word, .bool] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans actual.word_input_types

theorem ActualHeader.word_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.wordRow.row) : actual.header.function.resultType = closureType .word := by
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same]
  exact observed.wordResultType

theorem ActualHeader.bool_input_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.boolRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.bool, .word] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.boolShape.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    observed.boolShape.firstScheme, observed.boolShape.secondScheme, TypeSystem.Scheme.mono] using inputs.symm

theorem ActualHeader.bool_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.boolRow.row) : actual.header.types = [.bool, .word] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans actual.bool_input_types

theorem ActualHeader.bool_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.boolRow.row) : actual.header.function.resultType = closureType .bool := by
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same]
  exact observed.boolResultType

def ObservedStages.descriptor_at {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    {observed : ObservedRow fixture signature} (stages : ObservedStages fixture observed)
    (actual : ActualHeader fixture observed.row) :
    SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named actual.header.named.signature.key) := by
  rw [actual.key]
  exact stages.descriptor

end Tests.SourceCoreEvidenceClosure
end

section
-- leanmerge: from Solcore.Test.SourceCoreEvidenceClosureSyntax
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreEvidenceClosure
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


section Factory
variable {function : CheckedFunction} {signature generic : ProgramFunctionSignature}
  {firstParameter secondParameter : TypeSystem.TypeParameterId} {firstType secondType : TypeSystem.Ty} {trait : ProgramTraitId}
  (shape : FactoryShape function signature generic firstParameter secondParameter firstType secondType trait)

theorem FactoryShape.body_shape :
    CallableIndexedOwnedPreparedStagedBranchingTree.Shape function.typedBody true [shape.statement.id] :=
  .returnValue [] shape.statementFound shape.statementForm

theorem FactoryShape.body_syntax
    (unique : NodeOccurrencesUnique function.typedBody)
    {approved : ExpressionId → Prop} (leaf : approved shape.call.value.node.id)
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType function.typedBody {returnType := firstType} context
      [shape.statement.id] final facts) :
    GenericImperativeMatch.Syntax function.typedBody approved context
      (.statements true [shape.statement.id]) firstType := by
  obtain ⟨_, _, _, returned, _⟩ := head_tail typed
  have original := form_at unique shape.statementFound returned
  rw [shape.statementForm] at original
  cases original with
  | returnValue expression =>
    exact .body (.returnValue [] shape.statementFound shape.statementForm
      shape.statementType shape.call.value.found shape.call.value.type
      (by simpa only [shape.call.value.type] using expression) leaf)
end Factory
end Tests.SourceCoreEvidenceClosure
end

section
-- leanmerge: from Solcore.Test.SourceCoreEvidenceClosureFactorySupport
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreEvidenceClosure
open Solcore Frontend SourceInference SourceSemantics CoreLowering

structure ObservedFactory (fixture : CompiledFixture)
    {function signature generic firstParameter secondParameter firstType secondType trait}
    (shape : FactoryShape function signature generic firstParameter secondParameter firstType secondType trait) where
  owned : shape.expression.id.occurrence.owner = function.typedBody.owner
  reported : Core.Ty
  read : SourceCoreCompatibleDataExpressions.readExpression fixture.recipe.compiled.compatible.checked
    function.typedBody shape.expression.id = .ok (shape.expression, reported)

private def confirm (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

def observeFactorySupport (fixture : CompiledFixture)
    {function signature generic firstParameter secondParameter firstType secondType trait}
    (shape : FactoryShape function signature generic firstParameter secondParameter firstType secondType trait) :
    IO (ObservedFactory fixture shape) := do
  let ⟨owned⟩ ← confirm (shape.expression.id.occurrence.owner = function.typedBody.owner) "factory lambda owner"
  match read : SourceCoreCompatibleDataExpressions.readExpression fixture.recipe.compiled.compatible.checked
      function.typedBody shape.expression.id with
  | .error error => throw (IO.userError (reprStr error))
  | .ok (node, reported) =>
    let ⟨same⟩ ← confirm (node = shape.expression) "factory lambda node"
    return ⟨owned, reported, by simpa only [same] using read⟩

structure ObservedFactories (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  word : ObservedFactory fixture observed.factoryWordShape
  bool : ObservedFactory fixture observed.factoryBoolShape

def observeFactories (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedFactories fixture observed) := do
  return ⟨← observeFactorySupport fixture observed.factoryWordShape,
    ← observeFactorySupport fixture observed.factoryBoolShape⟩

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  {signature : ProgramFunctionSignature} {row : ObservedRow fixture signature}
  {generic : ProgramFunctionSignature} {firstParameter secondParameter : TypeSystem.TypeParameterId}
  {firstType secondType : TypeSystem.Ty} {trait : ProgramTraitId}

include observed in
theorem ActualHeader.factory_formation (actual : ActualHeader fixture row.row)
    (shape : FactoryShape row.row.function signature generic firstParameter secondParameter firstType secondType trait)
    (extra : ObservedFactory fixture shape) (stages : ObservedStages fixture row)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (expression : terminal.expression = shape.expression.id)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (included : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics reason token → faults reason token) :
    Nonempty (CallableIndexedOwnedContextualLambdaFormationReceipts.OrdinaryFormation
      (registry := registry) (faults := faults) actual.header actual.header.context actual.header.function.evidence
      (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) := by
  apply CallableIndexedOwnedPreparedNamedBranchingBodyLambdaFormation.of_terminal terminal
    fixture.recipePrepared diagnostic receiver included fixture.source_wellFormed observed.profile (stages.selected actual)
    observed.wordRow.entryMember (node := shape.expression) (reported := extra.reported)
  · rw [actual.source, expression]; exact shape.expressionFound
  · exact shape.lambda
  · rw [actual.source, expression]; exact extra.owned
  · exact shape.requirements
  · exact shape.coercions
  · simp only [observed.noLocals, List.find?_nil]
  · rw [actual.source, expression]; exact extra.read
  · rw [actual.source]; exact .returnValue [] shape.statementFound shape.statementForm
  · intro context final facts typed
    rw [actual.source] at typed ⊢
    exact shape.body_syntax (actual.source ▸ actual.header.unique) True.intro typed

include observed in
theorem ActualHeader.factory_support (actual : ActualHeader fixture row.row)
    (shape : FactoryShape row.row.function signature generic firstParameter secondParameter firstType secondType trait)
    (extra : ObservedFactory fixture shape) (stages : ObservedStages fixture row)
    (headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)))
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) headers)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (included : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics reason token → faults reason token) :
    ∃ terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header,
      terminal.expression = shape.expression.id ∧
      Nonempty (CallableIndexedOwnedPreparedStagedNamedBodySupport.Support headers
        (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) registry actual.header
        stages.registry terminal faults) := by
  obtain ⟨terminal, diagnostic, expression, point⟩ :=
    actual.terminal shape.expression.id shape.outerReturn shape.roots shape.outerFound shape.outerForm
  obtain ⟨formation⟩ := actual.factory_formation (observed := observed) shape extra stages terminal diagnostic expression receiver included
  exact ⟨terminal, expression, ⟨.formation (CallableIndexedOwnedPreparedStagedNamedBodySupport.Formation.of_actual
    headers (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
    registry actual.header stages.registry terminal faults point complete
    (bootstrap_zero fixture.recipe.compiled) formation fixture.source_wellFormed)⟩⟩

end Tests.SourceCoreEvidenceClosure
end

section
-- leanmerge: from Solcore.Test.SourceCoreEvidenceClosureFamily
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreEvidenceClosure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)

/-- The actual cached slot identifies one of the six prepared Source rows. -/
theorem ObservedProgram.cached_source {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (wordHeader : ActualHeader fixture observed.wordRow.row)
    (boolHeader : ActualHeader fixture observed.boolRow.row)
    (factoryWordHeader : ActualHeader fixture observed.factoryWordRow.row)
    (factoryBoolHeader : ActualHeader fixture observed.factoryBoolRow.row)
    (chooseWordHeader : ActualHeader fixture observed.chooseWordRow.row)
    (chooseBoolHeader : ActualHeader fixture observed.chooseBoolRow.row)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : fixture.recipe.compiled.indexed.base.functions[index]? = some named) :
    CallableIndexedNamedGeneration.source named = observed.wordRow.row.function.typedBody ∨
    CallableIndexedNamedGeneration.source named = observed.boolRow.row.function.typedBody ∨
    CallableIndexedNamedGeneration.source named = observed.factoryWordRow.row.function.typedBody ∨
    CallableIndexedNamedGeneration.source named = observed.factoryBoolRow.row.function.typedBody ∨
    CallableIndexedNamedGeneration.source named = observed.chooseWordRow.row.function.typedBody ∨
    CallableIndexedNamedGeneration.source named = observed.chooseBoolRow.row.function.typedBody := by
  have length : fixture.recipe.compiled.indexed.base.functions.length = 6 := by
    simpa only [CallableIndexedPreparedInventories.cached_globals, List.length_map] using observed.globalsLength
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  rw [length] at bound
  have casesIndex : index = observed.wordRow.index ∨
      index = observed.boolRow.index ∨
      index = observed.factoryWordRow.index ∨
      index = observed.factoryBoolRow.index ∨
      index = observed.chooseWordRow.index ∨
      index = observed.chooseBoolRow.index := by
    have contained := of_decide_eq_true (List.all_eq_true.mp observed.indexCoverage index (List.mem_range.mpr bound))
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using contained
  rcases casesIndex with same | same | same | same | same | same
  · left
    have actualIndex := (observed.wordRow.prepared_slot wordHeader.prepared).2
    rw [same, ← actualIndex, wordHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) wordHeader.prepared.same
  · right; left
    have actualIndex := (observed.boolRow.prepared_slot boolHeader.prepared).2
    rw [same, ← actualIndex, boolHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) boolHeader.prepared.same
  · right; right; left
    have actualIndex := (observed.factoryWordRow.prepared_slot factoryWordHeader.prepared).2
    rw [same, ← actualIndex, factoryWordHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) factoryWordHeader.prepared.same
  · right; right; right; left
    have actualIndex := (observed.factoryBoolRow.prepared_slot factoryBoolHeader.prepared).2
    rw [same, ← actualIndex, factoryBoolHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) factoryBoolHeader.prepared.same
  · right; right; right; right; left
    have actualIndex := (observed.chooseWordRow.prepared_slot chooseWordHeader.prepared).2
    rw [same, ← actualIndex, chooseWordHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) chooseWordHeader.prepared.same
  · right; right; right; right; right
    have actualIndex := (observed.chooseBoolRow.prepared_slot chooseBoolHeader.prepared).2
    rw [same, ← actualIndex, chooseBoolHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) chooseBoolHeader.prepared.same

private theorem root_no_lambda
    {function signature generic firstParameter secondParameter firstType secondType trait}
    (shape : RootShape function signature generic firstParameter secondParameter firstType secondType trait)
    (nodes : function.typedBody.nodes = shape.nodeList)
    {id node parameters result body}
    (found : ContainsExpression function.typedBody id node)
    (form : node.form = .lambda parameters result body) : False := by
  have member := found.1
  rw [nodes, RootShape.nodeList] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same | same | same
  all_goals try cases same
  · rw [shape.firstRead.form] at form; cases form
  · rw [shape.secondRead.form] at form; cases form
  · rw [shape.call.calleeForm] at form; cases form
  · rw [shape.call.form] at form; cases form

private theorem selected_no_lambda {function firstType secondType}
    (shape : SelectedShape function firstType secondType)
    (nodes : function.typedBody.nodes = shape.nodeList)
    {id node parameters result body}
    (found : ContainsExpression function.typedBody id node)
    (form : node.form = .lambda parameters result body) : False := by
  have member := found.1
  rw [nodes, SelectedShape.nodeList] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same
  · cases same; rw [shape.read.form] at form; cases form
  · cases same

theorem CompiledFixture.no_principal (fixture : CompiledFixture)
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal fixture.recipe.compiled method) : False := by
  obtain ⟨_implementation, _method, _trait, _definition, _substitution, instantiated⟩ := principal.source_instantiation
  cases instantiated with
  | intro _ _ _ _ member _ _ _ _ _ _ _ =>
    simp only [Program.ofChecked, fixture.sameProgram, fixture.methods, List.map_nil,
      List.not_mem_nil] at member

private theorem factory_lambda_shape
    {function signature generic firstParameter secondParameter firstType secondType trait}
    (shape : FactoryShape function signature generic firstParameter secondParameter firstType secondType trait)
    (nodes : function.typedBody.nodes = shape.nodeList)
    {id node parameters result body}
    (found : function.typedBody.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result body) :
    parameters = [] ∧ result = firstType ∧ body = [shape.statement.id] := by
  rcases shape.expressions nodes found with same | same | same | same | same
  all_goals subst node
  · rw [shape.firstRead.form] at form; cases form
  · rw [shape.secondRead.form] at form; cases form
  · rw [shape.call.calleeForm] at form; cases form
  · rw [shape.call.form] at form; cases form
  · rw [shape.lambda] at form
    obtain ⟨parametersEq, resultEq, bodyEq⟩ := ExpressionForm.lambda.inj form
    exact ⟨parametersEq.symm, resultEq.symm, bodyEq.symm⟩

private theorem factory_packet {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    {signature : ProgramFunctionSignature} {row : ObservedRow fixture signature}
    {generic firstParameter secondParameter firstType secondType trait}
    (shape : FactoryShape row.row.function signature generic firstParameter secondParameter firstType secondType trait)
    (nodes : row.row.function.typedBody.nodes = shape.nodeList)
    (ordinary : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported
      fixture.recipe.compiled.indexed.base.plan shape.call.instantiation)
    (signatureMember : signature ∈ fixture.recipe.compiled.sourceProgram.signatures.functions)
    {inputs : List (Input fixture.recipe.compiled)} (rows : Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) (headers rows))
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    {registry : SourceCoreRawMetadata.Registry}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : CallableIndexedLambdaValues.Code fixture.recipe.compiled.indexed function scope administrative)
    (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics))
    (provenance : CallableIndexedOwnedContextualLambdaProvenance.OrdinaryAt code support)
    (sameSource : function.source = row.row.function.typedBody) :
    Nonempty (Σ packet : CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.Packet code
        (RecursiveNamedPreparedStageScopes.registry stagePrepared),
      CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.Support (headers rows) code support.body.toContext
        (RecursiveNamedPreparedStageScopes.registry stagePrepared) packet
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  have found := code.sourceFound
  rw [sameSource] at found
  have lambda := factory_lambda_shape shape nodes found code.sourceForm
  have bodyShape := lambda.2.2
  have resultShape := lambda.2.1
  have bodyTree : CallableIndexedOwnedPreparedStagedBranchingTree.Shape function.source true function.body := by
    rw [sameSource, bodyShape]; exact shape.body_shape
  obtain ⟨_final, _facts, bodyTyped, _completes⟩ := CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters
    support.body.frame support.body.extended
  have tree : GenericImperativeMatch.Syntax function.source
      (fun id => CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax function.source id
        (CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported fixture.recipe.compiled.indexed.base.plan))
      support.body.context (.statements true function.body) function.resultType := by
    rw [sameSource, bodyShape, resultShape] at bodyTyped ⊢
    exact shape.body_syntax (sameSource ▸ support.unique) (shape.syntax ordinary) bodyTyped
  have metadata : CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles.MetadataFor
      fixture.recipe.compiled.indexed support.caller.named function.source
      (CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported fixture.recipe.compiled.indexed.base.plan) := by
    rw [sameSource]; exact shape.metadata nodes support.caller.named observed.noLocals
  obtain ⟨sidecar, _issued, selected⟩ :=
    CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code support.source_receipt support.body.unique
  exact CallableIndexedOwnedPreparedStagedOrdinaryEvidenceScopedSupport.of_actual
    stagePrepared code support provenance receiver fixture.source_wellFormed
    (fun instantiation accepted => by simpa only [support.compilation, CallableIndexedNamedGeneration.context, CompatibleNamedBody.bodyContext] using accepted)
    metadata rows complete signatureMember (by rw [sameSource]; exact row.sourceOwner)
    bodyTree tree.prepared _ (.anonymous selected)

def ObservedProgram.family {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (wordHeader : ActualHeader fixture observed.wordRow.row)
    (boolHeader : ActualHeader fixture observed.boolRow.row)
    (factoryWordHeader : ActualHeader fixture observed.factoryWordRow.row)
    (factoryBoolHeader : ActualHeader fixture observed.factoryBoolRow.row)
    (chooseWordHeader : ActualHeader fixture observed.chooseWordRow.row)
    (chooseBoolHeader : ActualHeader fixture observed.chooseBoolRow.row)
    {inputs : List (Input fixture.recipe.compiled)} (rows : Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) (headers rows))
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    {registry : SourceCoreRawMetadata.Registry}
    {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association (headers rows)
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      mapping world function native bindings parameter result) :
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor stagePrepared association := by
  cases association with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
    apply CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor.compiled
    have found := code.sourceFound
    rcases observed.cached_source wordHeader boolHeader factoryWordHeader factoryBoolHeader chooseWordHeader chooseBoolHeader
      support.caller.selected with original | original | original | original | original | original
    · rw [support.source.trans original] at found
      exact False.elim (root_no_lambda observed.wordShape observed.wordNodes (lookupExpression?_sound found) code.sourceForm)
    · rw [support.source.trans original] at found
      exact False.elim (root_no_lambda observed.boolShape observed.boolNodes (lookupExpression?_sound found) code.sourceForm)
    · obtain ⟨packet, supported⟩ := factory_packet observed observed.factoryWordShape observed.factoryWordNodes
        observed.factoryWord_supported (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.head _))
        rows complete stagePrepared receiver code support provenance (support.source.trans original)
      exact ⟨⟨packet, CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.SupportFor.of_generic _ _ _ supported⟩⟩
    · obtain ⟨packet, supported⟩ := factory_packet observed observed.factoryBoolShape observed.factoryBoolNodes
        observed.factoryBool_supported (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.head _))
        rows complete stagePrepared receiver code support provenance (support.source.trans original)
      exact ⟨⟨packet, CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.SupportFor.of_generic _ _ _ supported⟩⟩
    · rw [support.source.trans original] at found
      exact False.elim (selected_no_lambda observed.chooseWordShape observed.chooseWordNodes (lookupExpression?_sound found) code.sourceForm)
    · rw [support.source.trans original] at found
      exact False.elim (selected_no_lambda observed.chooseBoolShape observed.chooseBoolNodes (lookupExpression?_sound found) code.sourceForm)
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    exact False.elim (fixture.no_principal support.principal)

end Tests.SourceCoreEvidenceClosure
end

section
-- leanmerge: from Solcore.Test.SourceCoreEvidenceClosureSupports
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreEvidenceClosure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body of_terminal)
open CallableIndexedOwnedPreparedStagedNamedBodiesSupport (Support)

theorem actualStagePrepared (fixture : CompiledFixture) :
    RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable :=
  RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
    fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected

structure StaticSupportPackage (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (registry : SourceCoreRawMetadata.Registry)
    (completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed) where
  wordInput : Input fixture.recipe.compiled
  boolInput : Input fixture.recipe.compiled
  factoryWordInput : Input fixture.recipe.compiled
  factoryBoolInput : Input fixture.recipe.compiled
  chooseWordInput : Input fixture.recipe.compiled
  chooseBoolInput : Input fixture.recipe.compiled
  wordRow : wordInput.row = observed.wordRow.row
  boolRow : boolInput.row = observed.boolRow.row
  factoryWordRow : factoryWordInput.row = observed.factoryWordRow.row
  factoryBoolRow : factoryBoolInput.row = observed.factoryBoolRow.row
  chooseWordRow : chooseWordInput.row = observed.chooseWordRow.row
  chooseBoolRow : chooseBoolInput.row = observed.chooseBoolRow.row
  wordPacket : Issued wordInput
  boolPacket : Issued boolInput
  factoryWordPacket : Issued factoryWordInput
  factoryBoolPacket : Issued factoryBoolInput
  chooseWordPacket : Issued chooseWordInput
  chooseBoolPacket : Issued chooseBoolInput
  wordHeader : ActualHeader fixture observed.wordRow.row
  boolHeader : ActualHeader fixture observed.boolRow.row
  factoryWordHeader : ActualHeader fixture observed.factoryWordRow.row
  factoryBoolHeader : ActualHeader fixture observed.factoryBoolRow.row
  chooseWordHeader : ActualHeader fixture observed.chooseWordRow.row
  chooseBoolHeader : ActualHeader fixture observed.chooseBoolRow.row
  wordEq : wordHeader.header = wordPacket.header
  boolEq : boolHeader.header = boolPacket.header
  factoryWordEq : factoryWordHeader.header = factoryWordPacket.header
  factoryBoolEq : factoryBoolHeader.header = factoryBoolPacket.header
  chooseWordEq : chooseWordHeader.header = chooseWordPacket.header
  chooseBoolEq : chooseBoolHeader.header = chooseBoolPacket.header
  rows : Inventory [wordInput, boolInput, factoryWordInput, factoryBoolInput, chooseWordInput, chooseBoolInput]
  rowsEq : rows = (.cons wordPacket (.cons boolPacket (.cons factoryWordPacket (.cons factoryBoolPacket (.cons chooseWordPacket (.cons chooseBoolPacket .nil))))))
  complete : RecursiveNamedCatalogNativeContexts.Complete
    (values := .initial fixture.recipe.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) (headers rows)
  distinct : ([wordInput, boolInput, factoryWordInput, factoryBoolInput, chooseWordInput, chooseBoolInput].map (fun input => input.prepared.index)).Nodup
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
  wordDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named wordHeader.header.named.signature.key)
  boolDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named boolHeader.header.named.signature.key)
  factoryWordDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named factoryWordHeader.header.named.signature.key)
  factoryBoolDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named factoryBoolHeader.header.named.signature.key)
  chooseWordDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named chooseWordHeader.header.named.signature.key)
  chooseBoolDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named chooseBoolHeader.header.named.signature.key)

theorem StaticSupportPackage.header_list {fixture : CompiledFixture}
    {observed : ObservedProgram fixture} {registry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (support : StaticSupportPackage fixture observed registry completion) :
    headers support.rows = [support.wordHeader.header, support.boolHeader.header, support.factoryWordHeader.header, support.factoryBoolHeader.header, support.chooseWordHeader.header, support.chooseBoolHeader.header] := by
  rw [support.rowsEq]
  simp only [headers, support.wordEq, support.boolEq, support.factoryWordEq, support.factoryBoolEq, support.chooseWordEq, support.chooseBoolEq]

private def selectSix {compiled : SourceCoreUnifiedCompilation.Compiled}
    {word bool factoryWord factoryBool chooseWord chooseBool : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (wordBool : word.slot ≠ bool.slot)
    (wordFactoryWord : word.slot ≠ factoryWord.slot)
    (wordFactoryBool : word.slot ≠ factoryBool.slot)
    (wordChooseWord : word.slot ≠ chooseWord.slot)
    (wordChooseBool : word.slot ≠ chooseBool.slot)
    (boolFactoryWord : bool.slot ≠ factoryWord.slot)
    (boolFactoryBool : bool.slot ≠ factoryBool.slot)
    (boolChooseWord : bool.slot ≠ chooseWord.slot)
    (boolChooseBool : bool.slot ≠ chooseBool.slot)
    (factoryWordFactoryBool : factoryWord.slot ≠ factoryBool.slot)
    (factoryWordChooseWord : factoryWord.slot ≠ chooseWord.slot)
    (factoryWordChooseBool : factoryWord.slot ≠ chooseBool.slot)
    (factoryBoolChooseWord : factoryBool.slot ≠ chooseWord.slot)
    (factoryBoolChooseBool : factoryBool.slot ≠ chooseBool.slot)
    (chooseWordChooseBool : chooseWord.slot ≠ chooseBool.slot)
    (property : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → Type)
    (wordValue : property word)
    (boolValue : property bool)
    (factoryWordValue : property factoryWord)
    (factoryBoolValue : property factoryBool)
    (chooseWordValue : property chooseWord)
    (chooseBoolValue : property chooseBool)
    : ∀ header, header ∈ [word, bool, factoryWord, factoryBool, chooseWord, chooseBool] → property header := by
  intro header member
  if wordSlot : header.slot = word.slot then
    have same : header = word := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same | same | same | same
      · exact same
      · exact False.elim (wordBool (wordSlot.symm.trans (congrArg (·.slot) same)))
      · exact False.elim (wordFactoryWord (wordSlot.symm.trans (congrArg (·.slot) same)))
      · exact False.elim (wordFactoryBool (wordSlot.symm.trans (congrArg (·.slot) same)))
      · exact False.elim (wordChooseWord (wordSlot.symm.trans (congrArg (·.slot) same)))
      · exact False.elim (wordChooseBool (wordSlot.symm.trans (congrArg (·.slot) same)))
    exact same.symm ▸ wordValue
  else if boolSlot : header.slot = bool.slot then
    have same : header = bool := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same | same | same | same
      · exact False.elim (wordSlot (congrArg (·.slot) same))
      · exact same
      · exact False.elim (boolFactoryWord (boolSlot.symm.trans (congrArg (·.slot) same)))
      · exact False.elim (boolFactoryBool (boolSlot.symm.trans (congrArg (·.slot) same)))
      · exact False.elim (boolChooseWord (boolSlot.symm.trans (congrArg (·.slot) same)))
      · exact False.elim (boolChooseBool (boolSlot.symm.trans (congrArg (·.slot) same)))
    exact same.symm ▸ boolValue
  else if factoryWordSlot : header.slot = factoryWord.slot then
    have same : header = factoryWord := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same | same | same | same
      · exact False.elim (wordSlot (congrArg (·.slot) same))
      · exact False.elim (boolSlot (congrArg (·.slot) same))
      · exact same
      · exact False.elim (factoryWordFactoryBool (factoryWordSlot.symm.trans (congrArg (·.slot) same)))
      · exact False.elim (factoryWordChooseWord (factoryWordSlot.symm.trans (congrArg (·.slot) same)))
      · exact False.elim (factoryWordChooseBool (factoryWordSlot.symm.trans (congrArg (·.slot) same)))
    exact same.symm ▸ factoryWordValue
  else if factoryBoolSlot : header.slot = factoryBool.slot then
    have same : header = factoryBool := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same | same | same | same
      · exact False.elim (wordSlot (congrArg (·.slot) same))
      · exact False.elim (boolSlot (congrArg (·.slot) same))
      · exact False.elim (factoryWordSlot (congrArg (·.slot) same))
      · exact same
      · exact False.elim (factoryBoolChooseWord (factoryBoolSlot.symm.trans (congrArg (·.slot) same)))
      · exact False.elim (factoryBoolChooseBool (factoryBoolSlot.symm.trans (congrArg (·.slot) same)))
    exact same.symm ▸ factoryBoolValue
  else if chooseWordSlot : header.slot = chooseWord.slot then
    have same : header = chooseWord := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same | same | same | same
      · exact False.elim (wordSlot (congrArg (·.slot) same))
      · exact False.elim (boolSlot (congrArg (·.slot) same))
      · exact False.elim (factoryWordSlot (congrArg (·.slot) same))
      · exact False.elim (factoryBoolSlot (congrArg (·.slot) same))
      · exact same
      · exact False.elim (chooseWordChooseBool (chooseWordSlot.symm.trans (congrArg (·.slot) same)))
    exact same.symm ▸ chooseWordValue
  else
    have same : header = chooseBool := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same | same | same | same
      · exact False.elim (wordSlot (congrArg (·.slot) same))
      · exact False.elim (boolSlot (congrArg (·.slot) same))
      · exact False.elim (factoryWordSlot (congrArg (·.slot) same))
      · exact False.elim (factoryBoolSlot (congrArg (·.slot) same))
      · exact False.elim (chooseWordSlot (congrArg (·.slot) same))
      · exact same
    exact same.symm ▸ chooseBoolValue

theorem static_supports (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedFactories fixture observed)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (factoryWordStages : ObservedStages fixture observed.factoryWordRow)
    (factoryBoolStages : ObservedStages fixture observed.factoryBoolRow)
    (chooseWordStages : ObservedStages fixture observed.chooseWordRow)
    (chooseBoolStages : ObservedStages fixture observed.chooseBoolRow)
    (registry : SourceCoreRawMetadata.Registry)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics) :
    Nonempty (StaticSupportPackage fixture observed registry completion) := by
  obtain ⟨wordInput, boolInput, factoryWordInput, factoryBoolInput, chooseWordInput, chooseBoolInput, wordRow, boolRow, factoryWordRow, factoryBoolRow, chooseWordRow, chooseBoolRow, wordPacket, boolPacket, factoryWordPacket, factoryBoolPacket, chooseWordPacket, chooseBoolPacket, wordHeader, boolHeader, factoryWordHeader, factoryBoolHeader, chooseWordHeader, chooseBoolHeader, wordEq, boolEq, factoryWordEq, factoryBoolEq, chooseWordEq, chooseBoolEq, complete⟩ := observed.inventory
  let rows : Inventory [wordInput, boolInput, factoryWordInput, factoryBoolInput, chooseWordInput, chooseBoolInput] := (.cons wordPacket (.cons boolPacket (.cons factoryWordPacket (.cons factoryBoolPacket (.cons chooseWordPacket (.cons chooseBoolPacket .nil))))))
  have headerList : headers rows = [wordHeader.header, boolHeader.header, factoryWordHeader.header, factoryBoolHeader.header, chooseWordHeader.header, chooseBoolHeader.header] := by
    simp only [rows, headers, wordEq, boolEq, factoryWordEq, factoryBoolEq, chooseWordEq, chooseBoolEq]
  have wordIndex : wordHeader.header.slot = observed.wordRow.index :=
    wordHeader.aligned.slot.trans (observed.wordRow.prepared_slot wordHeader.prepared).2
  have wordInputIndex : wordHeader.header.slot = wordInput.prepared.index := by
    rw [wordEq]; exact wordPacket.aligned.slot
  have boolIndex : boolHeader.header.slot = observed.boolRow.index :=
    boolHeader.aligned.slot.trans (observed.boolRow.prepared_slot boolHeader.prepared).2
  have boolInputIndex : boolHeader.header.slot = boolInput.prepared.index := by
    rw [boolEq]; exact boolPacket.aligned.slot
  have factoryWordIndex : factoryWordHeader.header.slot = observed.factoryWordRow.index :=
    factoryWordHeader.aligned.slot.trans (observed.factoryWordRow.prepared_slot factoryWordHeader.prepared).2
  have factoryWordInputIndex : factoryWordHeader.header.slot = factoryWordInput.prepared.index := by
    rw [factoryWordEq]; exact factoryWordPacket.aligned.slot
  have factoryBoolIndex : factoryBoolHeader.header.slot = observed.factoryBoolRow.index :=
    factoryBoolHeader.aligned.slot.trans (observed.factoryBoolRow.prepared_slot factoryBoolHeader.prepared).2
  have factoryBoolInputIndex : factoryBoolHeader.header.slot = factoryBoolInput.prepared.index := by
    rw [factoryBoolEq]; exact factoryBoolPacket.aligned.slot
  have chooseWordIndex : chooseWordHeader.header.slot = observed.chooseWordRow.index :=
    chooseWordHeader.aligned.slot.trans (observed.chooseWordRow.prepared_slot chooseWordHeader.prepared).2
  have chooseWordInputIndex : chooseWordHeader.header.slot = chooseWordInput.prepared.index := by
    rw [chooseWordEq]; exact chooseWordPacket.aligned.slot
  have chooseBoolIndex : chooseBoolHeader.header.slot = observed.chooseBoolRow.index :=
    chooseBoolHeader.aligned.slot.trans (observed.chooseBoolRow.prepared_slot chooseBoolHeader.prepared).2
  have chooseBoolInputIndex : chooseBoolHeader.header.slot = chooseBoolInput.prepared.index := by
    rw [chooseBoolEq]; exact chooseBoolPacket.aligned.slot
  have wordBool : wordHeader.header.slot ≠ boolHeader.header.slot := by
    rw [wordIndex, boolIndex]; exact observed.wordBool
  have wordBoolInput : wordInput.prepared.index ≠ boolInput.prepared.index := by
    rw [← wordInputIndex, ← boolInputIndex]; exact wordBool
  have wordFactoryWord : wordHeader.header.slot ≠ factoryWordHeader.header.slot := by
    rw [wordIndex, factoryWordIndex]; exact observed.wordFactoryWord
  have wordFactoryWordInput : wordInput.prepared.index ≠ factoryWordInput.prepared.index := by
    rw [← wordInputIndex, ← factoryWordInputIndex]; exact wordFactoryWord
  have wordFactoryBool : wordHeader.header.slot ≠ factoryBoolHeader.header.slot := by
    rw [wordIndex, factoryBoolIndex]; exact observed.wordFactoryBool
  have wordFactoryBoolInput : wordInput.prepared.index ≠ factoryBoolInput.prepared.index := by
    rw [← wordInputIndex, ← factoryBoolInputIndex]; exact wordFactoryBool
  have wordChooseWord : wordHeader.header.slot ≠ chooseWordHeader.header.slot := by
    rw [wordIndex, chooseWordIndex]; exact observed.wordChooseWord
  have wordChooseWordInput : wordInput.prepared.index ≠ chooseWordInput.prepared.index := by
    rw [← wordInputIndex, ← chooseWordInputIndex]; exact wordChooseWord
  have wordChooseBool : wordHeader.header.slot ≠ chooseBoolHeader.header.slot := by
    rw [wordIndex, chooseBoolIndex]; exact observed.wordChooseBool
  have wordChooseBoolInput : wordInput.prepared.index ≠ chooseBoolInput.prepared.index := by
    rw [← wordInputIndex, ← chooseBoolInputIndex]; exact wordChooseBool
  have boolFactoryWord : boolHeader.header.slot ≠ factoryWordHeader.header.slot := by
    rw [boolIndex, factoryWordIndex]; exact observed.boolFactoryWord
  have boolFactoryWordInput : boolInput.prepared.index ≠ factoryWordInput.prepared.index := by
    rw [← boolInputIndex, ← factoryWordInputIndex]; exact boolFactoryWord
  have boolFactoryBool : boolHeader.header.slot ≠ factoryBoolHeader.header.slot := by
    rw [boolIndex, factoryBoolIndex]; exact observed.boolFactoryBool
  have boolFactoryBoolInput : boolInput.prepared.index ≠ factoryBoolInput.prepared.index := by
    rw [← boolInputIndex, ← factoryBoolInputIndex]; exact boolFactoryBool
  have boolChooseWord : boolHeader.header.slot ≠ chooseWordHeader.header.slot := by
    rw [boolIndex, chooseWordIndex]; exact observed.boolChooseWord
  have boolChooseWordInput : boolInput.prepared.index ≠ chooseWordInput.prepared.index := by
    rw [← boolInputIndex, ← chooseWordInputIndex]; exact boolChooseWord
  have boolChooseBool : boolHeader.header.slot ≠ chooseBoolHeader.header.slot := by
    rw [boolIndex, chooseBoolIndex]; exact observed.boolChooseBool
  have boolChooseBoolInput : boolInput.prepared.index ≠ chooseBoolInput.prepared.index := by
    rw [← boolInputIndex, ← chooseBoolInputIndex]; exact boolChooseBool
  have factoryWordFactoryBool : factoryWordHeader.header.slot ≠ factoryBoolHeader.header.slot := by
    rw [factoryWordIndex, factoryBoolIndex]; exact observed.factoryWordFactoryBool
  have factoryWordFactoryBoolInput : factoryWordInput.prepared.index ≠ factoryBoolInput.prepared.index := by
    rw [← factoryWordInputIndex, ← factoryBoolInputIndex]; exact factoryWordFactoryBool
  have factoryWordChooseWord : factoryWordHeader.header.slot ≠ chooseWordHeader.header.slot := by
    rw [factoryWordIndex, chooseWordIndex]; exact observed.factoryWordChooseWord
  have factoryWordChooseWordInput : factoryWordInput.prepared.index ≠ chooseWordInput.prepared.index := by
    rw [← factoryWordInputIndex, ← chooseWordInputIndex]; exact factoryWordChooseWord
  have factoryWordChooseBool : factoryWordHeader.header.slot ≠ chooseBoolHeader.header.slot := by
    rw [factoryWordIndex, chooseBoolIndex]; exact observed.factoryWordChooseBool
  have factoryWordChooseBoolInput : factoryWordInput.prepared.index ≠ chooseBoolInput.prepared.index := by
    rw [← factoryWordInputIndex, ← chooseBoolInputIndex]; exact factoryWordChooseBool
  have factoryBoolChooseWord : factoryBoolHeader.header.slot ≠ chooseWordHeader.header.slot := by
    rw [factoryBoolIndex, chooseWordIndex]; exact observed.factoryBoolChooseWord
  have factoryBoolChooseWordInput : factoryBoolInput.prepared.index ≠ chooseWordInput.prepared.index := by
    rw [← factoryBoolInputIndex, ← chooseWordInputIndex]; exact factoryBoolChooseWord
  have factoryBoolChooseBool : factoryBoolHeader.header.slot ≠ chooseBoolHeader.header.slot := by
    rw [factoryBoolIndex, chooseBoolIndex]; exact observed.factoryBoolChooseBool
  have factoryBoolChooseBoolInput : factoryBoolInput.prepared.index ≠ chooseBoolInput.prepared.index := by
    rw [← factoryBoolInputIndex, ← chooseBoolInputIndex]; exact factoryBoolChooseBool
  have chooseWordChooseBool : chooseWordHeader.header.slot ≠ chooseBoolHeader.header.slot := by
    rw [chooseWordIndex, chooseBoolIndex]; exact observed.chooseWordChooseBool
  have chooseWordChooseBoolInput : chooseWordInput.prepared.index ≠ chooseBoolInput.prepared.index := by
    rw [← chooseWordInputIndex, ← chooseBoolInputIndex]; exact chooseWordChooseBool
  obtain ⟨wordTerminal, _wordExpression, ⟨wordSupport⟩⟩ :=
    wordHeader.word_support observed rows complete receiver (actualStagePrepared fixture)
  obtain ⟨boolTerminal, _boolExpression, ⟨boolSupport⟩⟩ :=
    boolHeader.bool_support observed rows complete receiver (actualStagePrepared fixture)
  obtain ⟨factoryWordTerminal, _factoryWordExpression, ⟨factoryWordSupport⟩⟩ :=
    factoryWordHeader.factory_support (observed := observed) observed.factoryWordShape extra.word factoryWordStages (headers rows) complete receiver (fun _ _ represented => represented)
  obtain ⟨factoryBoolTerminal, _factoryBoolExpression, ⟨factoryBoolSupport⟩⟩ :=
    factoryBoolHeader.factory_support (observed := observed) observed.factoryBoolShape extra.bool factoryBoolStages (headers rows) complete receiver (fun _ _ represented => represented)
  obtain ⟨chooseWordTerminal, _chooseWordExpression, ⟨chooseWordSupport⟩⟩ :=
    chooseWordHeader.chooseWord_support observed receiver (actualStagePrepared fixture)
  obtain ⟨chooseBoolTerminal, _chooseBoolExpression, ⟨chooseBoolSupport⟩⟩ :=
    chooseBoolHeader.chooseBool_support observed receiver (actualStagePrepared fixture)
  let property := fun header => Σ terminal : Body header,
    Support (headers rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) terminal
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
  let choose : ∀ header, header ∈ headers rows → property header := fun header member =>
    selectSix wordBool wordFactoryWord wordFactoryBool wordChooseWord wordChooseBool boolFactoryWord boolFactoryBool boolChooseWord boolChooseBool factoryWordFactoryBool factoryWordChooseWord factoryWordChooseBool factoryBoolChooseWord factoryBoolChooseBool chooseWordChooseBool property
      ⟨of_terminal wordTerminal, .canonical wordSupport⟩ ⟨of_terminal boolTerminal, .canonical boolSupport⟩ ⟨of_terminal factoryWordTerminal, factoryWordSupport⟩ ⟨of_terminal factoryBoolTerminal, factoryBoolSupport⟩ ⟨of_terminal chooseWordTerminal, .recursive chooseWordSupport⟩ ⟨of_terminal chooseBoolTerminal, .recursive chooseBoolSupport⟩ header (headerList ▸ member)
  exact ⟨{
    wordInput := wordInput
    boolInput := boolInput
    factoryWordInput := factoryWordInput
    factoryBoolInput := factoryBoolInput
    chooseWordInput := chooseWordInput
    chooseBoolInput := chooseBoolInput
    wordRow := wordRow
    boolRow := boolRow
    factoryWordRow := factoryWordRow
    factoryBoolRow := factoryBoolRow
    chooseWordRow := chooseWordRow
    chooseBoolRow := chooseBoolRow
    wordPacket := wordPacket
    boolPacket := boolPacket
    factoryWordPacket := factoryWordPacket
    factoryBoolPacket := factoryBoolPacket
    chooseWordPacket := chooseWordPacket
    chooseBoolPacket := chooseBoolPacket
    wordHeader := wordHeader
    boolHeader := boolHeader
    factoryWordHeader := factoryWordHeader
    factoryBoolHeader := factoryBoolHeader
    chooseWordHeader := chooseWordHeader
    chooseBoolHeader := chooseBoolHeader
    wordEq := wordEq
    boolEq := boolEq
    factoryWordEq := factoryWordEq
    factoryBoolEq := factoryBoolEq
    chooseWordEq := chooseWordEq
    chooseBoolEq := chooseBoolEq
    rows := rows
    complete := complete
    rowsEq := rfl
    distinct := by simp [wordBoolInput, wordFactoryWordInput, wordFactoryBoolInput, wordChooseWordInput, wordChooseBoolInput, boolFactoryWordInput, boolFactoryBoolInput, boolChooseWordInput, boolChooseBoolInput, factoryWordFactoryBoolInput, factoryWordChooseWordInput, factoryWordChooseBoolInput, factoryBoolChooseWordInput, factoryBoolChooseBoolInput, chooseWordChooseBoolInput]
    terminals := fun header member => (choose header member).1
    supports := fun header member => (choose header member).2
    family := fun association => observed.family wordHeader boolHeader factoryWordHeader factoryBoolHeader chooseWordHeader chooseBoolHeader rows complete (actualStagePrepared fixture) receiver association
    wordDescriptor := wordStages.descriptor_at wordHeader
    boolDescriptor := boolStages.descriptor_at boolHeader
    factoryWordDescriptor := factoryWordStages.descriptor_at factoryWordHeader
    factoryBoolDescriptor := factoryBoolStages.descriptor_at factoryBoolHeader
    chooseWordDescriptor := chooseWordStages.descriptor_at chooseWordHeader
    chooseBoolDescriptor := chooseBoolStages.descriptor_at chooseBoolHeader
  }⟩

end Tests.SourceCoreEvidenceClosure
end

section
-- leanmerge: from Solcore.Test.SourceCoreEvidenceClosureCommon
/-! Genuine initial diagnostics and current retained public sessions. No
independent native execution is used to construct the semantic receiver. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreEvidenceClosure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open RecursiveNamedPublicFunctionHistory (Entry)

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


structure ObservedReceiver (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics
  registry : completion.result.context.registry = fixture.recipe.compiled.compatible.checked.staticRegistry

/-- The receiver is built directly at the genuine initial metadata registry. -/
theorem initial_receiver (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    Nonempty (ObservedReceiver fixture observed) := by
  obtain ⟨receiver, _entry, registry, issued⟩ :=
    CallableIndexedOwnedPublicFaultReceivers.Receiver.at_registry fixture.recipe.compiled observed.wordRow.entry
      fixture.recipe.compiled.compatible.checked.staticRegistry (.refl _)
  exact ⟨⟨receiver, issued, registry⟩⟩


abbrev PublicSupports {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (receiver : ObservedReceiver fixture observed) :=
  StaticSupportPackage fixture observed receiver.completion.result.context.registry receiver.completion

def PublicSupports.bodies {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :=
  support.terminals

def PublicSupports.functions {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :=
  CallableIndexedOwnedContextualCellOrigins.functions (headers support.rows)
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
    (CallableIndexedOwnedContextualCellOrigins.functions_include_general observed.profile origin)

structure RetainedState {fixture : CompiledFixture} {observed : ObservedProgram fixture}
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
    support.wordHeader.header session mapping world heap store caller entries

def SourceCall {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (arguments : List Dynamic.Value)
    (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ rawD function size,
    CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD function ∧
    Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) size invocation
      support.wordHeader.header.function.context before (.global function) arguments outcome after

theorem word_bool_inputs {entries : List Entry} {context : SourceSemantics.Context}
    (word : Core.Word) (flag : Bool) :
    RecursiveNamedPublicFunctionHistoryInputs.Inputs entries context [.word, .bool]
      [.word word, .bool flag] [.word word, .bool flag] := by
  exact .cons (.data
    ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩
    ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩)
    (.cons (.data
      ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩
      ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩) .nil)

theorem bool_word_inputs {entries : List Entry} {context : SourceSemantics.Context}
    (flag : Bool) (word : Core.Word) :
    RecursiveNamedPublicFunctionHistoryInputs.Inputs entries context [.bool, .word]
      [.bool flag, .word word] [.bool flag, .word word] := by
  exact .cons (.data
    ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩
    ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩)
    (.cons (.data
      ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩
      ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩) .nil)

theorem word_bool_simple (word : Core.Word) (flag : Bool) :
    ∀ value ∈ ([.word word, .bool flag] : List SourceCorePublicValues.Value),
      SourceCoreIndexedSession.SimplePublic value := by
  intro value member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact .word word
  · exact .bool flag

theorem bool_word_simple (flag : Bool) (word : Core.Word) :
    ∀ value ∈ ([.bool flag, .word word] : List SourceCorePublicValues.Value),
      SourceCoreIndexedSession.SimplePublic value := by
  intro value member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact .bool flag
  · exact .word word

end Tests.SourceCoreEvidenceClosure
end

section
-- leanmerge: from Solcore.Test.SourceCoreEvidenceClosureInvocation
/-! Collected closure handles use the current metadata receiver.
Each returned state retains that receiver for the following public call. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreEvidenceClosure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

def SourceInvocation {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (source : Dynamic.Value)
    (arguments : List Dynamic.Value) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ size, Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) size invocation
    support.wordHeader.header.function.context before source arguments outcome after

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
      support.wordHeader.header.function.context parameter argument packedSource)
    (call : ObservedInvocation publicSession handle argument)
    {word : Core.Word} (returned : call.completion.value = .word word)
    (invocation : Staging.Recursive.Scope) :
    ∃ (sources : List Dynamic.Value) (after : RetainedState support call.completion.session entries),
      Dynamic.ValuesPack sources packedSource ∧
      SourceInvocation support invocation state.heap entry.source sources (.value (.word word)) after.heap := by
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨receiving, checkpoint, actual, generation, value, finalStore, actualParameter, actualResult,
      nativeParameter, nativeResult, callable, packed, encodedValues, sources, sourceSize, outcome,
      after, finalMap, finalWorld, reached, contextAt, issued, extended, _diagnostics,
      started, _parameterView, _resultView, succeeded, actualAt, packing, trace, result,
      _related, retained, returnedRegistry⟩ :=
    RecursiveNamedPublicActualRegistryReflection.public_invoke_succeeded
      (completion := state.receiving) state.issued (actualStagePrepared fixture) observed.profile
      support.observations semantic support.family
      support.bodies
      support.supports fixture.source_wellFormed state.history entry member entryType
      input state.atRecipe state.registry state.atSession
      (by simpa only [entryHandle] using call.executed) invocation
  have handleType : entry.handle.sourceType = .function parameter .word := entryHandle ▸ handleType
  have requested := started.requested_exact handleType
  have signature := started.selected.signature handleType
  have projected := started.resultProjection
  rw [signature.2] at projected
  have nativeResultEq : nativeResult = .word := (Except.ok.inj projected).symm
  rw [nativeResultEq] at result
  have outcomeValue := RecursiveNamedPublicWordResultMeaning.represented_word succeeded requested
    (actualAt.1.symm.trans returned) result.1
  let next : RetainedState support call.completion.session entries := {
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
    registry := (congrArg (·.registry) contextAt).symm ▸ returnedRegistry
    history := retained }
  exact ⟨sources, next, packing, sourceSize, by simpa only [outcomeValue] using trace⟩




/-- Current history supplies the callee; literal input rows supply its argument.
No registry equality, arbitrary receiving table or metadata extension is assumed. -/
theorem invoke_bool {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries)
    {parameter : TypeSystem.Ty}
    (entryType : entry.sourceType = .function parameter .bool)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    (handleType : handle.sourceType = .function parameter .bool)
    {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries
      support.wordHeader.header.function.context parameter argument packedSource)
    (call : ObservedInvocation publicSession handle argument)
    {flag : Bool} (returned : call.completion.value = .bool flag)
    (invocation : Staging.Recursive.Scope) :
    ∃ (sources : List Dynamic.Value) (after : RetainedState support call.completion.session entries),
      Dynamic.ValuesPack sources packedSource ∧
      SourceInvocation support invocation state.heap entry.source sources (.value (.bool flag)) after.heap := by
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨receiving, checkpoint, actual, generation, value, finalStore, actualParameter, actualResult,
      nativeParameter, nativeResult, callable, packed, encodedValues, sources, sourceSize, outcome,
      after, finalMap, finalWorld, reached, contextAt, issued, extended, _diagnostics,
      started, _parameterView, _resultView, succeeded, actualAt, packing, trace, result,
      _related, retained, returnedRegistry⟩ :=
    RecursiveNamedPublicActualRegistryReflection.public_invoke_succeeded
      (completion := state.receiving) state.issued (actualStagePrepared fixture) observed.profile
      support.observations semantic support.family
      support.bodies
      support.supports fixture.source_wellFormed state.history entry member entryType
      input state.atRecipe state.registry state.atSession
      (by simpa only [entryHandle] using call.executed) invocation
  have handleType : entry.handle.sourceType = .function parameter .bool := entryHandle ▸ handleType
  have requested := started.requested_exact handleType
  have signature := started.selected.signature handleType
  have projected := started.resultProjection
  rw [signature.2] at projected
  have nativeResultEq : nativeResult = .bool := (Except.ok.inj projected).symm
  rw [nativeResultEq] at result
  have outcomeValue := Tests.SourceCoreEvidenceDirect.represented_bool succeeded requested
    (actualAt.1.symm.trans returned) result.1
  let next : RetainedState support call.completion.session entries := {
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
    registry := (congrArg (·.registry) contextAt).symm ▸ returnedRegistry
    history := retained }
  exact ⟨sources, next, packing, sourceSize, by simpa only [outcomeValue] using trace⟩





end Tests.SourceCoreEvidenceClosure
end

section
-- leanmerge: from Solcore.Test.SourceCoreEvidenceClosureMakeStep
/-! A genuine successful public factory call extends the current retained
history with its actual new closure. The next state is the returned session,
including the original captured heap and encoder metadata. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreEvidenceClosure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open RecursiveNamedPublicFunctionHistory (Entry)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
  {publicArtifact : SourceCoreExecution.Artifact}
  {publicSession : SourceCoreExecution.Session publicArtifact} {entries : List Entry}

/-- An actual public factory call constructs Source execution and the next history.
Every older entry remains in order, followed by this call's exported handle. -/
theorem RetainedState.make_typed_handle
    (state : RetainedState support publicSession entries)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (call : ObservedFunctionCall publicSession key publicArguments)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers support.rows) fixture.recipePrepared
      call.checkpoint state.session key publicArguments runOptions.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key))
    (invocation : Staging.Recursive.Scope) :
    ∃ entry : Entry, entry.sourceType = request.header.function.resultType ∧ entry.handle = call.handle ∧
      call.handle.sourceType = request.header.function.resultType ∧
      ∃ after : RetainedState support call.completion.session (entries ++ [entry]),
        SourceCall support request.header invocation state.heap arguments
          (.value entry.source) after.heap := by
  have registryAt : request.encodedValues.registry =
      state.receiving.result.context.registry := by
    exact request.started.simple_registry state.registry simple
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨actual, generation, nativeValue, finalStore, capture,
    sourceSize, outcome, heap, mapping, world, succeeded, valueEq, typeEq, budgetEq,
    returnedAt, trace, result, caller, source, payload, sourceValue, nativePayload, related, continued⟩ :=
    CallableIndexedOwnedPreparedStagedHistoryPublicContinuations.public_run_succeeded_remembers
      (inputs := [support.wordInput, support.boolInput, support.factoryWordInput, support.factoryBoolInput, support.chooseWordInput, support.chooseBoolInput]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture)
      (completion := state.receiving)
      (receiver := state.issued)
      (profile := observed.profile)
      (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (extension := state.receiving.result.extension)
      (semantic := semantic)
      (family := support.family) (namedTerminals := support.bodies) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := fixture.recipePrepared)
      (selected := request.selected) (caller := state.caller) (history := state.history)
      (atCheckpoint := request.atCheckpoint) (started := request.started)
      (invocation := invocation) (inputReceipts := inputs)
      (metadata := by rw [registryAt]; exact .refl _)
      (sourceAt := request.sourceAt)
      call.started call.executed call.returned descriptor
  let entry : Entry := ⟨request.header.function.resultType, source, call.handle, payload,
    request.header.output, runOptions.outputValidationFuel⟩
  let after : RetainedState support call.completion.session (entries ++ [entry]) := {
    artifact := state.artifact
    session := actual.session
    mapping := mapping
    world := world
    heap := heap
    store := finalStore
    caller := caller
    atSession := returnedAt
    atRecipe := state.atRecipe
    receiving := state.receiving
    issued := state.issued
    extension := state.extension
    registry := by
      have registered := request.started.returned_registry succeeded
      rw [registryAt] at registered
      exact registered
    history := continued }
  have atRecipe : state.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType] at requested
  have handleType := succeeded.function_source_type requested (valueEq.symm.trans call.returned)
  refine ⟨entry, rfl, rfl, handleType, after, request.rawD, request.function, sourceSize, request.sourceAt, ?_⟩
  simpa only [entry, after, sourceValue] using trace

end Tests.SourceCoreEvidenceClosure
end

section
-- leanmerge: from Solcore.Test.SourceCoreEvidenceClosureSeed
/-! Actual initialization and the first public wordRoot execution establish
the first Source closure and history entry, including its captured local cell. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreEvidenceClosure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicFunctionHistory (Entry)

theorem first_meaning_typed_handle {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    (support : PublicSupports receiver)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (first : ObservedPublicRun fixture observed.wordRow.toObservedRow) :
    ∃ entry : Entry,
      entry.sourceType = (closureType .word) ∧ entry.handle = first.handle ∧
      first.handle.sourceType = (closureType .word) ∧
      ∃ state : RetainedState support first.completion.session [entry],
        SourceCall support support.wordHeader.header
          (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
          ⟨[]⟩ [.word seed, .bool true] (.value entry.source) state.heap := by
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ :=
    fixture.actual_start first.opened first.started
  have ready : first.bootstrap.ReadyAt 100000 first.session := .single first.ready
  obtain ⟨_bootstrap, initialized, _value, _initialStore, _atBootstrap, initial,
      initializedAt, _done, booted⟩ := ready.indexed opened first.fresh
  have same : initialized = session := initializedAt.unique sessionAt
  subst initialized
  have startupRegistry : encodedValues.registry = fixture.recipe.compiled.compatible.checked.staticRegistry := by
    apply started.simple_registry (booted.registry_at initial)
    exact word_bool_simple seed true
  obtain ⟨selectedHeader, selected⟩ := started.selection prepared support.complete
  have selectedEq : selectedHeader = support.wordHeader.header := by
    apply selected_word_root (fixture := fixture) (observed := observed)
      support.wordHeader support.boolHeader support.factoryWordHeader support.factoryBoolHeader support.chooseWordHeader support.chooseBoolHeader (root := root) (header := selectedHeader)
    · exact support.header_list ▸ selected
    · exact of_decide_eq_true (List.find?_some (p := fun candidate : SourceCoreIndexedSession.Root fixture.recipe.compiled =>
        decide (candidate.key = observed.wordRow.row.key)) started.selected)
  subst selectedHeader
  have inputs : RecursiveNamedPublicNestedInputs.Inputs support.rows session support.wordHeader.header.function.context
      (support.wordHeader.header.bindings.map (fun binding => binding.1.scheme.body)) [.word seed, .bool true] [.word seed, .bool true] := by
    rw [support.wordHeader.word_input_types]
    exact .cons (.leaf (.data ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩))
      (.cons (.leaf (.data ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩
        ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩)) .nil)
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiver.completion.result.context.registry := by
    rw [startupRegistry]
    exact receiver.completion.result.extension
  have sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt support.wordHeader.header support.wordInput.prepared.available
      (CallableNamedReversal.global (CallableNamedMetadata.global support.wordPacket.header.named.specialized support.wordInput.prepared.available)) := by
    rw [support.wordEq]
    exact support.wordPacket.sourceAt
  obtain ⟨caller, returnedCompletion, generation, value, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, _fullResult,
      returnedCaller, source, payload, sourceValue, _nativeValue, _related, retained⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedHistoryPublicSeed.public_run_succeeded_remembers
      (inputs := [support.wordInput, support.boolInput, support.factoryWordInput, support.factoryBoolInput, support.chooseWordInput, support.chooseBoolInput]) (rows := support.rows) (distinct := support.distinct)
      (stagePrepared := actualStagePrepared fixture)
      (completion := receiver.completion)
      (receiver := receiver.issued)
      (profile := observed.profile) (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := support.bodies) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := prepared) (selected := selected)
      (opened := opened) (fresh := first.fresh) (ready := .single first.ready)
      (sameRuntime := SourceCoreExecution.Session.SameRuntime.refl first.session) (atSession := sessionAt)
      (atCheckpoint := checkpointAt) (started := started) (inputReceipts := inputs)
      (metadata := metadata) (sourceAt := sourceAt)
      (invocation := RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
      first.started first.executed first.returned support.wordDescriptor
  let entry : Entry := ⟨support.wordHeader.header.function.resultType, source, first.handle,
    payload, support.wordHeader.header.output, runOptions.outputValidationFuel⟩
  have returnedRegistry := started.returned_registry succeeded
  rw [startupRegistry] at returnedRegistry
  let state : RetainedState support first.completion.session [entry] := {
    artifact := artifact
    session := returnedCompletion.session
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
  have atRecipe : artifact.RecipeAt fixture.recipe := by
    cases artifact
    exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2
  rw [resultType, support.wordHeader.word_result_type] at requested
  have handleType := succeeded.function_source_type requested (valueEq.symm.trans first.returned)
  refine ⟨entry, support.wordHeader.word_result_type, rfl, handleType, state, ?_⟩
  exact ⟨support.wordInput.prepared.available, _, sourceSize, sourceAt, sourceValue ▸ trace⟩

/-- The original factory theorem remains available when the public handle's
raw type is not needed by the caller. -/
theorem first_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    (support : PublicSupports receiver)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (first : ObservedPublicRun fixture observed.wordRow.toObservedRow) :
    ∃ entry : Entry,
      entry.sourceType = (closureType .word) ∧ entry.handle = first.handle ∧
      ∃ state : RetainedState support first.completion.session [entry],
        SourceCall support support.wordHeader.header
          (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
          ⟨[]⟩ [.word seed, .bool true] (.value entry.source) state.heap := by
  obtain ⟨entry, sourceType, handle, _handleType, state, trace⟩ :=
    first_meaning_typed_handle support wordStages first
  exact ⟨entry, sourceType, handle, state, trace⟩

end Tests.SourceCoreEvidenceClosure
end

section
-- leanmerge: from Solcore.Test.SourceCoreEvidenceClosurePublicExecution
/-! Seven actual public calls retain three distinct closures, both scalar result
profiles, and every intermediate Source heap in the returned session history. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreEvidenceClosure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

structure SequenceWitness {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) where
  support : PublicSupports receiver
  first : Entry
  second : Entry
  third : Entry
  firstType : first.sourceType = closureType .word
  secondType : second.sourceType = closureType .bool
  thirdType : third.sourceType = closureType .word
  firstHandle : first.handle = sequence.first.handle
  secondHandle : second.handle = sequence.second.handle
  thirdHandle : third.handle = sequence.third.handle
  firstHandleType : sequence.first.handle.sourceType = closureType .word
  secondHandleType : sequence.second.handle.sourceType = closureType .bool
  thirdHandleType : sequence.third.handle.sourceType = closureType .word
  firstSecond : first.handle ≠ second.handle
  firstThird : first.handle ≠ third.handle
  secondThird : second.handle ≠ third.handle
  initial : RetainedState support sequence.first.completion.session [first]
  secondState : RetainedState support sequence.second.completion.session [first, second]
  firstReadState : RetainedState support sequence.firstRead.completion.session [first, second]
  thirdState : RetainedState support sequence.third.completion.session [first, second, third]
  secondReadState : RetainedState support sequence.secondRead.completion.session [first, second, third]
  repeatedReadState : RetainedState support sequence.repeatedRead.completion.session [first, second, third]
  finalState : RetainedState support sequence.thirdRead.completion.session [first, second, third]
  firstTrace : SourceCall support support.wordHeader.header
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
    ⟨[]⟩ [.word seed, .bool true] (.value first.source) initial.heap
  secondTrace : SourceCall support support.boolHeader.header
    (RecursiveStageRegistry.scope boolStages.sidecar [] support.boolHeader.header.function)
    initial.heap [.bool false, .word (Core.Word.ofNatModulo 22)] (.value second.source) secondState.heap
  firstArguments : List Dynamic.Value
  firstPacking : Dynamic.ValuesPack firstArguments .unit
  firstReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
    secondState.heap first.source firstArguments (.value (.word seed)) firstReadState.heap
  thirdTrace : SourceCall support support.wordHeader.header
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
    firstReadState.heap [.word (Core.Word.ofNatModulo 33), .bool false] (.value third.source) thirdState.heap
  secondArguments : List Dynamic.Value
  secondPacking : Dynamic.ValuesPack secondArguments .unit
  secondReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
    thirdState.heap second.source secondArguments (.value (.bool false)) secondReadState.heap
  repeatedArguments : List Dynamic.Value
  repeatedPacking : Dynamic.ValuesPack repeatedArguments .unit
  repeatedReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
    secondReadState.heap first.source repeatedArguments (.value (.word seed)) repeatedReadState.heap
  thirdArguments : List Dynamic.Value
  thirdPacking : Dynamic.ValuesPack thirdArguments .unit
  thirdReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
    repeatedReadState.heap third.source thirdArguments (.value (.word (Core.Word.ofNatModulo 33))) finalState.heap

theorem sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedFactories fixture observed)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (factoryWordStages : ObservedStages fixture observed.factoryWordRow)
    (factoryBoolStages : ObservedStages fixture observed.factoryBoolRow)
    (chooseWordStages : ObservedStages fixture observed.chooseWordRow)
    (chooseBoolStages : ObservedStages fixture observed.chooseBoolRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    Nonempty (SequenceWitness wordStages boolStages sequence receiver) := by
  obtain ⟨support⟩ := static_supports fixture observed extra wordStages boolStages factoryWordStages factoryBoolStages
    chooseWordStages chooseBoolStages receiver.completion.result.context.registry receiver.issued
  let scope := RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function
  let boolScope := RecursiveStageRegistry.scope boolStages.sidecar [] support.boolHeader.header.function
  obtain ⟨first, firstType, firstHandle, firstHandleType, initial, firstTrace⟩ :=
    first_meaning_typed_handle support wordStages sequence.first
  obtain ⟨secondRequest⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.wordInput, support.boolInput, support.factoryWordInput,
      support.factoryBoolInput, support.chooseWordInput, support.chooseBoolInput] support.rows support.complete
    initial.atRecipe initial.history.current.1 initial.atSession sequence.second.started
  have secondHeader := selected_bool_at support.wordHeader support.boolHeader support.factoryWordHeader
    support.factoryBoolHeader support.chooseWordHeader support.chooseBoolHeader support.header_list secondRequest
  have secondInputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs [first] secondRequest.header.function.context
      (secondRequest.header.bindings.map (fun binding => binding.1.scheme.body))
      [.bool false, .word (Core.Word.ofNatModulo 22)] [.bool false, .word (Core.Word.ofNatModulo 22)] := by
    rw [secondHeader, support.boolHeader.bool_input_types]
    exact bool_word_inputs false _
  obtain ⟨second, secondType, secondHandle, secondHandleType, secondState, secondTrace⟩ :=
    initial.make_typed_handle sequence.second secondRequest secondInputs (bool_word_simple false _)
      (secondHeader.symm ▸ support.boolDescriptor) boolScope
  rw [secondHeader] at secondType secondHandleType secondTrace
  rw [support.boolHeader.bool_result_type] at secondType secondHandleType
  have unitInput : ∀ entries, RecursiveNamedPublicFunctionHistoryInputs.Input
      entries support.wordHeader.header.function.context .unit .unit .unit := fun _ =>
    .data ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
      ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
  obtain ⟨firstArguments, firstReadState, firstPacking, firstReadTrace⟩ := invoke_word secondState first
    (by simp) firstType firstHandle firstHandleType (unitInput _) sequence.firstRead sequence.firstValue scope
  obtain ⟨thirdRequest⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.wordInput, support.boolInput, support.factoryWordInput,
      support.factoryBoolInput, support.chooseWordInput, support.chooseBoolInput] support.rows support.complete
    firstReadState.atRecipe firstReadState.history.current.1 firstReadState.atSession sequence.third.started
  have thirdHeader := selected_word_at support.wordHeader support.boolHeader support.factoryWordHeader
    support.factoryBoolHeader support.chooseWordHeader support.chooseBoolHeader support.header_list thirdRequest
  have thirdInputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs [first, second] thirdRequest.header.function.context
      (thirdRequest.header.bindings.map (fun binding => binding.1.scheme.body))
      [.word (Core.Word.ofNatModulo 33), .bool false] [.word (Core.Word.ofNatModulo 33), .bool false] := by
    rw [thirdHeader, support.wordHeader.word_input_types]
    exact word_bool_inputs _ false
  obtain ⟨third, thirdType, thirdHandle, thirdHandleType, thirdState, thirdTrace⟩ :=
    firstReadState.make_typed_handle sequence.third thirdRequest thirdInputs (word_bool_simple _ false)
      (thirdHeader.symm ▸ support.wordDescriptor) scope
  rw [thirdHeader] at thirdType thirdHandleType thirdTrace
  rw [support.wordHeader.word_result_type] at thirdType thirdHandleType
  obtain ⟨secondArguments, secondReadState, secondPacking, secondReadTrace⟩ := invoke_bool thirdState second
    (by simp) secondType secondHandle secondHandleType (unitInput _) sequence.secondRead sequence.secondValue scope
  obtain ⟨repeatedArguments, repeatedReadState, repeatedPacking, repeatedReadTrace⟩ := invoke_word secondReadState first
    (by simp) firstType firstHandle firstHandleType (unitInput _) sequence.repeatedRead sequence.repeatedValue scope
  obtain ⟨thirdArguments, finalState, thirdPacking, thirdReadTrace⟩ := invoke_word repeatedReadState third
    (by simp) thirdType thirdHandle thirdHandleType (unitInput _) sequence.thirdRead sequence.thirdValue scope
  exact ⟨{
    support, first, second, third, firstType, secondType, thirdType,
    firstHandle, secondHandle, thirdHandle, firstHandleType, secondHandleType, thirdHandleType,
    firstSecond := by rw [firstHandle, secondHandle]; exact sequence.firstSecond
    firstThird := by rw [firstHandle, thirdHandle]; exact sequence.firstThird
    secondThird := by rw [secondHandle, thirdHandle]; exact sequence.secondThird
    initial, secondState, firstReadState, thirdState, secondReadState, repeatedReadState, finalState,
    firstTrace, secondTrace, firstArguments, firstPacking, firstReadTrace,
    thirdTrace, secondArguments, secondPacking, secondReadTrace,
    repeatedArguments, repeatedPacking, repeatedReadTrace, thirdArguments, thirdPacking, thirdReadTrace }⟩

theorem closed_sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedFactories fixture observed)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (factoryWordStages : ObservedStages fixture observed.factoryWordRow)
    (factoryBoolStages : ObservedStages fixture observed.factoryBoolRow)
    (chooseWordStages : ObservedStages fixture observed.chooseWordRow)
    (chooseBoolStages : ObservedStages fixture observed.chooseBoolRow)
    (sequence : ObservedSequence fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed, Nonempty (SequenceWitness wordStages boolStages sequence receiver) := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  exact ⟨receiver, sequence_meaning fixture observed extra wordStages boolStages factoryWordStages factoryBoolStages
    chooseWordStages chooseBoolStages sequence receiver⟩
end Tests.SourceCoreEvidenceClosure
end

section
-- leanmerge: from Solcore.Test.SourceCoreEvidenceClosureInitialForward
/-! Independent nested-direct Source success gives execution and export bounds
at the real first checkpoint, with the exact returned heap and a usable handle. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreEvidenceClosure
open Solcore Frontend SourceInference SourceSemantics CoreLowering

/-- The returned public value reimports to the exact represented Source result. -/
def ReturnedValue {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} (completion : SourceCoreExecution.Completion artifact)
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : RetainedState support completion.session entries) (rawType : TypeSystem.Ty) (source : Dynamic.Value) (fuel : Nat) : Prop :=
  ∃ payload nativeType,
    state.session.EncodesAt fuel rawType completion.value payload ∧
    CompatiblePayload.ValueRep fixture.recipe.compiled.compatible.checked state.receiving.result.context.registry
      support.functions state.mapping state.world rawType source payload nativeType

/-- Every sufficiently funded factory export is appended to the actual returned history. -/
def ReturnedHistory {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {artifact : SourceCoreExecution.Artifact} (completion : SourceCoreExecution.Completion artifact)
    (entries : List RecursiveNamedPublicFunctionHistory.Entry) (resultType : TypeSystem.Ty)
    (source : Dynamic.Value) (after : Dynamic.Heap) (fuel : Nat) : Prop :=
  ∃ entry : RecursiveNamedPublicFunctionHistory.Entry,
    entry.sourceType = closureType resultType ∧ entry.source = source ∧
    completion.value = .function entry.handle ∧ entry.handle.sourceType = closureType resultType ∧
    ∃ returned : RetainedState support completion.session (entries ++ [entry]),
      returned.heap = after ∧ ReturnedValue completion returned (closureType resultType) source fuel

/-- The initial entry exports its genuine raw result type and returns the exact
Source heap in a reusable session at every sufficient pair of fuel budgets. -/
def InitialForwardAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (first : ObservedPublicRun fixture observed.wordRow.toObservedRow) (source : Dynamic.Value) (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome first.artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      first.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion first.artifact,
        outcome = .succeeded completion ∧
        completion.session.ExportsReady ∧ ReturnedHistory support completion [] .word source after outputFuel

theorem forward_initial {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (first : ObservedPublicRun fixture observed.wordRow.toObservedRow)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {source : Dynamic.Value}
    (trace : SourceCall support support.wordHeader.header invocation ⟨[]⟩ [.word seed, .bool true] (.value source) after) :
    InitialForwardAt support first source after := by
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ := fixture.actual_start first.opened first.started
  obtain ⟨selectedHeader, selected⟩ := started.selection prepared support.complete
  have selectedEq : selectedHeader = support.wordHeader.header := by
    apply selected_word_root (fixture := fixture) (observed := observed)
      support.wordHeader support.boolHeader support.factoryWordHeader support.factoryBoolHeader support.chooseWordHeader support.chooseBoolHeader (root := root) (header := selectedHeader)
    · exact support.header_list ▸ selected
    · exact of_decide_eq_true (List.find?_some (p := fun candidate : SourceCoreIndexedSession.Root fixture.recipe.compiled =>
        decide (candidate.key = observed.wordRow.toObservedRow.row.key)) started.selected)
  subst selectedHeader
  have inputs : RecursiveNamedPublicNestedInputs.Inputs support.rows session support.wordHeader.header.function.context
      (support.wordHeader.header.bindings.map (fun binding => binding.1.scheme.body)) [.word seed, .bool true] [.word seed, .bool true] := by
    rw [support.wordHeader.word_input_types]
    exact .cons (.leaf (.data
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩))
      (.cons (.leaf (.data
        ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩
        ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩)) .nil)
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  obtain ⟨receiving, contextAt, issued, extended, _diagnostics, _caller, _capture,
      _payload, _finalStore, _finalMap, _finalWorld, requiredExecution, requiredOutput,
      _nativeEnough, _fullResult, publicEnough⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedOutputPreservation.public_resume_has_sufficient_fuel
      (inputs := [support.wordInput, support.boolInput, support.factoryWordInput, support.factoryBoolInput, support.chooseWordInput, support.chooseBoolInput]) (rows := support.rows) (distinct := support.distinct)
      (stagePrepared := actualStagePrepared fixture) (receiver := receiver.issued)
      (profile := observed.profile) (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (baseRegistry := receiver.registry)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := support.bodies)
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
  rw [rawResult] at requested
  have requestedRaw := requested
  rw [support.wordHeader.word_result_type] at requested
  have initialReady := (SourceCoreExecution.Bootstrap.ReadyAt.single first.ready).exportsReady first.authority
  have checkpointReady := started.original.initial_registry.exportsReady (sessionAt.exportsReady_iff.mp initialReady)
  refine ⟨requiredExecution, max requiredOutput 1, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, _generation, _reached, succeeded, exported, actualAt,
      _related, _history, registry, ready⟩ :=
    publicEnough executionFuel outputFuel outcome executionBound (Nat.le_trans (Nat.le_max_left _ _) outputBound) resumed
  obtain ⟨exportedCompletion, handle, sameOutcome, functionValue, handleType, _ready⟩ :=
    SourceCoreExecution.Checkpoint.ResumeAt.runtime_function_succeeded checkpointAt resumed checkpointReady
      (_nativeEnough executionFuel executionBound) requested rfl (by omega)
  have sameCompletion : exportedCompletion = completion := SourceCoreExecution.Outcome.succeeded.inj (sameOutcome.symm.trans succeeded)
  subst exportedCompletion
  let entry : RecursiveNamedPublicFunctionHistory.Entry :=
    ⟨support.wordHeader.header.function.resultType, source, handle, _payload, support.wordHeader.header.output, outputFuel⟩
  obtain ⟨returnedCaller, related, post⟩ := _fullResult.2.2.2.2.2.2.2
  have retained := RecursiveNamedPublicFunctionHistory.History.first rfl started selected exported _fullResult
    returnedCaller ⟨related, post⟩
    (.remember requestedRaw rfl rfl (actualAt.1.symm.trans functionValue))
  let returned : RetainedState support completion.session [entry] := {
    artifact := artifact
    session := actual.session
    mapping := _finalMap
    world := _finalWorld
    heap := after
    store := _finalStore
    caller := returnedCaller
    atSession := actualAt.2.2.2
    atRecipe := started.recipe_eq
    receiving := receiving
    issued := issued
    extension := extended
    registry := (congrArg (·.registry) contextAt).symm ▸ registry
    history := retained }
  have represented : CompatiblePayload.ValueRep fixture.recipe.compiled.compatible.checked receiving.result.context.registry
      support.functions _finalMap _finalWorld (closureType .word) source _payload support.wordHeader.header.output := by
    have result := _fullResult.2.1
    rw [support.wordHeader.word_result_type] at result
    cases result with | value represented => exact represented
  have encoded := (exported.reimports_payload requested rfl).2
  rw [← actualAt.1] at encoded
  exact ⟨completion, succeeded, actualAt.2.2.2.exportsReady_iff.mpr ready,
    entry, support.wordHeader.word_result_type, rfl, functionValue, handleType,
    returned, rfl, _payload, _, encoded, represented⟩



end Tests.SourceCoreEvidenceClosure
end

section
-- leanmerge: from Solcore.Test.SourceCoreEvidenceClosureInvocationForward
/-! The four captured closure calls establish independent Source traces.
Those traces imply actual public export on their original starts at every
sufficient execution and output-validation budget. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreEvidenceClosure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)
open Tests.SourceCoreEvidenceDirect (ScalarOutput)

def ForwardScalarAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {publicArtifact : SourceCoreExecution.Artifact} (publicSession : SourceCoreExecution.Session publicArtifact)
    (entries : List Entry) (handle : SourceCorePublicValues.Handle)
    (scalar : ScalarOutput) (after : Dynamic.Heap) : Prop :=
  ∃ checkpoint : SourceCoreExecution.Checkpoint publicArtifact,
    publicSession.startHandlePacked handle .unit runOptions.inputValidationFuel = .ok checkpoint ∧
    ∃ requiredExecution requiredOutput,
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
        checkpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ completion : SourceCoreExecution.Completion publicArtifact,
          outcome = .succeeded completion ∧ completion.value = scalar.publicValue ∧ completion.session.ExportsReady ∧
          ∃ returned : RetainedState support completion.session entries, returned.heap = after

theorem forward_scalar {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries) {scalar : ScalarOutput}
    (entryType : entry.sourceType = .function .unit scalar.sourceType)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    (handleType : handle.sourceType = .function .unit scalar.sourceType)
    (call : ObservedInvocation publicSession handle .unit)
    (exportsReady : publicSession.ExportsReady)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {arguments : List Dynamic.Value}
    (packing : Dynamic.ValuesPack arguments .unit)
    (trace : SourceInvocation support invocation state.heap entry.source arguments (.value scalar.source) after) :
    ForwardScalarAt support publicSession entries handle scalar after := by
  have unitInput : RecursiveNamedPublicFunctionHistoryInputs.Input entries
      support.wordHeader.header.function.context .unit .unit .unit :=
    .data ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
      ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
  obtain ⟨publicCheckpoint, accepted, _resumed⟩ := call.executed
  obtain ⟨checkpoint, atCheckpoint, original⟩ :=
    RecursiveNamedPublicDirectHandleMeaning.recover_handle_start state.atSession accepted
  have imported := (state.history.current.2.2.2.2 entry member).1
  rw [entryType, entryHandle] at imported
  obtain ⟨actualParameter, actualResult, nativeParameter, nativeResult, callable, packed, encodedValues,
      started, _parameterView, _resultView⟩ :=
    RecursiveNamedPublicDirectPackedInputMeaning.actual_start_compatible state.atRecipe
      state.history.current.1 imported original
  have signature := started.selected.signature handleType
  have requested := started.requested_exact handleType
  have projected := started.resultProjection
  rw [signature.2] at projected
  have nativeResultEq : nativeResult = scalar.nativeType := by
    cases scalar <;> exact (Except.ok.inj projected).symm
  subst nativeResult
  rw [← entryHandle] at started
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨size, trace⟩ := trace
  obtain ⟨receiving, contextAt, issued, extended, _diagnostics, requiredExecution, requiredOutput,
      payload, finalStore, finalMap, finalWorld, _nativeEnough, fullResult, publicEnough⟩ :=
    RecursiveNamedPublicActualRegistryOutputPreservation.public_resume_has_sufficient_fuel
      (completion := state.receiving) state.issued (actualStagePrepared fixture) observed.profile
      support.observations semantic support.family
      support.bodies
      support.supports fixture.source_wellFormed state.history entry member entryType
      unitInput state.registry (state.atSession.exportsReady_iff.mp exportsReady)
      started packing trace atCheckpoint
  have payloadEq : payload = scalar.native := by
    have represented := fullResult.1
    cases represented with
    | value related => exact scalar.native_value related
  subst payload
  refine ⟨publicCheckpoint, accepted, requiredExecution, requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome enoughExecution enoughOutput resumed
  obtain ⟨completion, actual, _generation, reached, succeeded, exported, atCompletion,
      _related, history, returnedRegistry, returnedReady⟩ :=
    publicEnough executionFuel outputFuel outcome enoughExecution enoughOutput resumed
  have valueEq : completion.value = scalar.publicValue :=
    atCompletion.1.trans (scalar.succeeded_value exported requested)
  let returned : RetainedState support completion.session entries := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := atCompletion.2.2.2
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := state.extension.trans extended
    registry := (congrArg (·.registry) contextAt).symm ▸ returnedRegistry
    history := history }
  exact ⟨completion, succeeded, valueEq, atCompletion.2.2.2.exportsReady_iff.mpr returnedReady, returned, rfl⟩

/-- Every retained closure invocation has bounds at its own genuine start. -/
def InvocationForwardMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
    {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness wordStages boolStages sequence receiver) : Prop :=
  ForwardScalarAt meaning.support sequence.second.completion.session [meaning.first, meaning.second]
    sequence.first.handle (.word seed) meaning.firstReadState.heap ∧
  ForwardScalarAt meaning.support sequence.third.completion.session [meaning.first, meaning.second, meaning.third]
    sequence.second.handle (.bool false) meaning.secondReadState.heap ∧
  ForwardScalarAt meaning.support sequence.secondRead.completion.session [meaning.first, meaning.second, meaning.third]
    sequence.first.handle (.word seed) meaning.repeatedReadState.heap ∧
  ForwardScalarAt meaning.support sequence.repeatedRead.completion.session [meaning.first, meaning.second, meaning.third]
    sequence.third.handle (.word (Core.Word.ofNatModulo 33)) meaning.finalState.heap

theorem SequenceWitness.invocations_forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
    {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness wordStages boolStages sequence receiver) : InvocationForwardMeaning meaning := by
  have initialReady := (SourceCoreExecution.Bootstrap.ReadyAt.single sequence.first.ready).exportsReady sequence.first.authority
  have firstReady := sequence.first.executed.exportsReady initialReady
  have secondReady := sequence.second.executed.exportsReady firstReady
  have firstReadReady := sequence.firstRead.executed.exportsReady secondReady
  have thirdReady := sequence.third.executed.exportsReady firstReadReady
  have secondReadReady := sequence.secondRead.executed.exportsReady thirdReady
  have repeatedReady := sequence.repeatedRead.executed.exportsReady secondReadReady
  exact ⟨forward_scalar (scalar := .word seed) meaning.secondState meaning.first (by simp)
      meaning.firstType meaning.firstHandle meaning.firstHandleType sequence.firstRead secondReady
      meaning.firstPacking meaning.firstReadTrace,
    forward_scalar (scalar := .bool false) meaning.thirdState meaning.second (by simp)
      meaning.secondType meaning.secondHandle meaning.secondHandleType sequence.secondRead thirdReady
      meaning.secondPacking meaning.secondReadTrace,
    forward_scalar (scalar := .word seed) meaning.secondReadState meaning.first (by simp)
      meaning.firstType meaning.firstHandle meaning.firstHandleType sequence.repeatedRead secondReadReady
      meaning.repeatedPacking meaning.repeatedReadTrace,
    forward_scalar (scalar := .word (Core.Word.ofNatModulo 33)) meaning.repeatedReadState meaning.third (by simp)
      meaning.thirdType meaning.thirdHandle meaning.thirdHandleType sequence.thirdRead repeatedReady
      meaning.thirdPacking meaning.thirdReadTrace⟩
end Tests.SourceCoreEvidenceClosure
end

section
-- leanmerge: from Solcore.Test.SourceCoreEvidenceClosureForward
/-! Following named execution derives sufficient public fuel from the independent
Source trace at the exact retained heap. The output and next history follow for
every sufficient resume of the original checkpoint. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreEvidenceClosure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

def ForwardAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry} {key : SourceCoreIndexedSession.Key}
    {publicArguments : List SourceCorePublicValues.Value}
    (call : ObservedFunctionCall session key publicArguments) (resultType : TypeSystem.Ty)
    (source : Dynamic.Value) (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion artifact,
        outcome = .succeeded completion ∧
        completion.session.ExportsReady ∧ ReturnedHistory support completion entries resultType source after outputFuel

theorem forward_make {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : RetainedState support session entries)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (call : ObservedFunctionCall session key publicArguments) (ready : session.ExportsReady)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers support.rows) fixture.recipePrepared
      call.checkpoint state.session key publicArguments runOptions.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value} {resultType : TypeSystem.Ty}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (resultTypeEq : request.header.function.resultType = closureType resultType)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {source : Dynamic.Value}
    (trace : SourceCall support request.header invocation state.heap
      arguments (.value source) after) :
    ForwardAt (entries := entries) support call resultType source after := by
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  obtain ⟨receiving, contextAt, issued, extended, _diagnostics, _capture,
      payload, finalStore, finalMap, finalWorld, requiredExecution, requiredOutput,
      _nativeEnough, fullResult, publicEnough⟩ :=
    RecursiveNamedPublicActualRegistryNamedOutputPreservation.public_resume_has_sufficient_fuel
      (inputs := [support.wordInput, support.boolInput, support.factoryWordInput, support.factoryBoolInput, support.chooseWordInput, support.chooseBoolInput]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture) (completion := state.receiving)
      (receiver := state.issued) (profile := observed.profile) (observations := support.observations)
      (semantic := semantic) (family := support.family)
      (namedTerminals := support.bodies) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := fixture.recipePrepared)
      (selected := request.selected) (caller := state.caller) (history := state.history)
      (atCheckpoint := request.atCheckpoint) (started := request.started)
      (inputReceipts := inputs) (atRegistry := state.registry)
      (exportsReady := state.atSession.exportsReady_iff.mp ready) (sourceAt := sourceAt) applied
  have atRecipe : state.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have rootResult := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [rootResult] at requested
  have requestedRaw := requested
  rw [resultTypeEq] at requested
  have checkpointReady := request.started.original.initial_registry.exportsReady (state.atSession.exportsReady_iff.mp ready)
  refine ⟨requiredExecution, max requiredOutput 1, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, _generation, _reached, succeeded, exported, actualAt,
      _related, _history, registry, returnedReady⟩ :=
    publicEnough executionFuel outputFuel outcome executionBound (Nat.le_trans (Nat.le_max_left _ _) outputBound) resumed
  obtain ⟨exportedCompletion, handle, sameOutcome, functionValue, handleType, _ready⟩ :=
    SourceCoreExecution.Checkpoint.ResumeAt.runtime_function_succeeded request.atCheckpoint resumed checkpointReady
      (_nativeEnough executionFuel executionBound) requested rfl (by omega)
  have sameCompletion : exportedCompletion = completion := SourceCoreExecution.Outcome.succeeded.inj (sameOutcome.symm.trans succeeded)
  subst exportedCompletion
  let entry : RecursiveNamedPublicFunctionHistory.Entry :=
    ⟨request.header.function.resultType, source, handle, payload, request.header.output, outputFuel⟩
  obtain ⟨returnedCaller, related, post⟩ := fullResult.2.2.2.2.2.2.2
  have prior := RecursiveNamedPublicHistoryRegistryExtension.extend_history state.history extended
  have retained := RecursiveNamedPublicFunctionHistory.History.next prior rfl request.started request.selected
    exported fullResult returnedCaller ⟨related, post⟩
    (.remember requestedRaw rfl rfl (actualAt.1.symm.trans functionValue))
  let returned : RetainedState support completion.session (entries ++ [entry]) := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := returnedCaller
    atSession := actualAt.2.2.2
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := state.extension.trans extended
    registry := (congrArg (·.registry) contextAt).symm ▸ registry
    history := retained }
  have represented : CompatiblePayload.ValueRep fixture.recipe.compiled.compatible.checked receiving.result.context.registry
      support.functions finalMap finalWorld (closureType resultType) source payload request.header.output := by
    have result := fullResult.2.1
    rw [resultTypeEq] at result
    cases result with | value represented => exact represented
  have encoded := (exported.reimports_payload requested rfl).2
  rw [← actualAt.1] at encoded
  exact ⟨completion, succeeded, actualAt.2.2.2.exportsReady_iff.mpr returnedReady,
    entry, resultTypeEq, rfl, functionValue, handleType, returned, rfl, payload, _, encoded, represented⟩


/-- The three factory executions derive bounds from their independent Source traces. -/
def ForwardMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
    {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness wordStages boolStages sequence receiver) : Prop :=
  InitialForwardAt meaning.support sequence.first meaning.first.source meaning.initial.heap ∧
  ForwardAt (entries := [meaning.first]) meaning.support sequence.second .bool meaning.second.source meaning.secondState.heap ∧
  ForwardAt (entries := [meaning.first, meaning.second]) meaning.support sequence.third .word
    meaning.third.source meaning.thirdState.heap

theorem SequenceWitness.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
    {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness wordStages boolStages sequence receiver) : ForwardMeaning meaning := by
  have ready := (SourceCoreExecution.Bootstrap.ReadyAt.single sequence.first.ready).exportsReady sequence.first.authority
  have firstReady := sequence.first.executed.exportsReady ready
  have secondReady := sequence.second.executed.exportsReady firstReady
  have readReady := sequence.firstRead.executed.exportsReady secondReady
  let support := meaning.support
  obtain ⟨secondRequest⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.wordInput, support.boolInput, support.factoryWordInput,
      support.factoryBoolInput, support.chooseWordInput, support.chooseBoolInput] support.rows support.complete
    meaning.initial.atRecipe meaning.initial.history.current.1 meaning.initial.atSession sequence.second.started
  have secondHeader := selected_bool_at support.wordHeader support.boolHeader support.factoryWordHeader
    support.factoryBoolHeader support.chooseWordHeader support.chooseBoolHeader support.header_list secondRequest
  have secondInputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs [meaning.first] secondRequest.header.function.context
      (secondRequest.header.bindings.map (fun binding => binding.1.scheme.body))
      [.bool false, .word (Core.Word.ofNatModulo 22)] [.bool false, .word (Core.Word.ofNatModulo 22)] := by
    rw [secondHeader, support.boolHeader.bool_input_types]
    exact bool_word_inputs false _
  have secondResult : secondRequest.header.function.resultType = closureType .bool := by
    rw [secondHeader]; exact support.boolHeader.bool_result_type
  have secondTrace : SourceCall support secondRequest.header
      (RecursiveStageRegistry.scope boolStages.sidecar [] support.boolHeader.header.function)
      meaning.initial.heap [.bool false, .word (Core.Word.ofNatModulo 22)] (.value meaning.second.source) meaning.secondState.heap := by
    rw [secondHeader]; exact meaning.secondTrace
  obtain ⟨thirdRequest⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.wordInput, support.boolInput, support.factoryWordInput,
      support.factoryBoolInput, support.chooseWordInput, support.chooseBoolInput] support.rows support.complete
    meaning.firstReadState.atRecipe meaning.firstReadState.history.current.1 meaning.firstReadState.atSession sequence.third.started
  have thirdHeader := selected_word_at support.wordHeader support.boolHeader support.factoryWordHeader
    support.factoryBoolHeader support.chooseWordHeader support.chooseBoolHeader support.header_list thirdRequest
  have thirdInputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs [meaning.first, meaning.second] thirdRequest.header.function.context
      (thirdRequest.header.bindings.map (fun binding => binding.1.scheme.body))
      [.word (Core.Word.ofNatModulo 33), .bool false] [.word (Core.Word.ofNatModulo 33), .bool false] := by
    rw [thirdHeader, support.wordHeader.word_input_types]
    exact word_bool_inputs _ false
  have thirdResult : thirdRequest.header.function.resultType = closureType .word := by
    rw [thirdHeader]; exact support.wordHeader.word_result_type
  have thirdTrace : SourceCall support thirdRequest.header
      (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
      meaning.firstReadState.heap [.word (Core.Word.ofNatModulo 33), .bool false] (.value meaning.third.source) meaning.thirdState.heap := by
    rw [thirdHeader]; exact meaning.thirdTrace
  exact ⟨forward_initial support sequence.first meaning.firstTrace,
    forward_make meaning.initial sequence.second firstReady secondRequest secondInputs secondResult secondTrace,
    forward_make meaning.firstReadState sequence.third readReady thirdRequest thirdInputs thirdResult thirdTrace⟩

theorem closed_forward_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedFactories fixture observed)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (factoryWordStages : ObservedStages fixture observed.factoryWordRow)
    (factoryBoolStages : ObservedStages fixture observed.factoryBoolRow)
    (chooseWordStages : ObservedStages fixture observed.chooseWordRow)
    (chooseBoolStages : ObservedStages fixture observed.chooseBoolRow)
    (sequence : ObservedSequence fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed,
      ∃ meaning : SequenceWitness wordStages boolStages sequence receiver,
        ForwardMeaning meaning ∧ InvocationForwardMeaning meaning := by
  obtain ⟨receiver, meaning⟩ := closed_sequence_meaning fixture observed extra wordStages boolStages factoryWordStages
    factoryBoolStages chooseWordStages chooseBoolStages sequence
  obtain ⟨meaning⟩ := meaning
  exact ⟨receiver, meaning, meaning.forward, meaning.invocations_forward⟩

def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let extra ← observeFactories fixture observed
  let wordStages ← observeStages fixture observed.wordRow.toObservedRow
  let boolStages ← observeStages fixture observed.boolRow.toObservedRow
  let factoryWordStages ← observeStages fixture observed.factoryWordRow
  let factoryBoolStages ← observeStages fixture observed.factoryBoolRow
  let chooseWordStages ← observeStages fixture observed.chooseWordRow
  let chooseBoolStages ← observeStages fixture observed.chooseBoolRow
  let sequence ← observeSequence fixture observed
  have _meaning := closed_forward_meaning fixture observed extra wordStages boolStages factoryWordStages
    factoryBoolStages chooseWordStages chooseBoolStages sequence
  IO.println "Evidence closure PASS: Aword11/Bboolfalse/A11/Cword33/Bfalse/A11/C33, three distinct handles, exact Source heaps/history, all seven public fuel bounds proved"
end Tests.SourceCoreEvidenceClosure
end
