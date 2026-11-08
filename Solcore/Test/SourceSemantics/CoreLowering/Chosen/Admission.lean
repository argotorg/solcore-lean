import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.MixedBodyCompiler
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.TerminalStatementOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LiteralReturns
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.IndirectExpressionHeads
import Solcore.Test.Frontend.Source.CompilerFeatureSupport
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogAndSpecialization
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedAllocation
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NamedCatalog
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.LambdaFormation
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CallEvidence
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.NestedEntries
import Solcore.SourceSemantics.CoreLowering.Internal.Diagnostics.EmittedPlans
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionGeneralBuiltins
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.OrdinaryLambdas
import Solcore.SourceSemantics.InferenceSoundness
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CoercionSpine

/-!
# Chosen ordinary admission tests

The accepted fixture of chosen ordinary calls: header, inventory, typing and admission.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedFixture
/-! The written fixture retains actual successful compiler equations, one
initializer-root parent action, numeric evidence, and finite graph/runtime
receipts. Lambda typing and full chosen-factory population remain separate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreChosenOrdinaryAcceptedFixture
open Solcore Frontend SourceInference SourceSemantics.CoreLowering Core
open SourceSemantics
open CallableIndexedNamedGeneration

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function accepted() returns (Word) { let f = lam(value: (Word, Word)) -> Word { return 7; }; return f((1, 2)); }"}] }

def effectiveDiagnostics (compiled : SourceCoreUnifiedCompilation.Compiled)
    (diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)) :
    SourceCoreDataPlaceFaultSites.Program :=
  match compiled.indexed.base.callableContext with
  | none => diagnostics.program
  | some native => {diagnostics.program with rootTable := native.diagnostics.rootTable}

def namedAction (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : Named)
    (diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)) :=
  SourceCoreGeneralFunctions.compileClosureWithRepresentation compiled.indexed.base.sourceProgram
    (representation compiled.indexed) compiled.indexed.base.sourceProgram.signatures
    compiled.indexed.base.plan compiled.indexed.base.globals (effectiveDiagnostics compiled diagnostics)
    compiled.indexed.base.locals compiled.indexed.base.callableContext compiled.indexed.fuel named

/-- These are equations for the untouched public preparation and real named
slot. No runtime expression is substituted and no success equation is erased. -/
structure Packet where
  program : CheckedProgram
  checked : checkProgram workspace = .ok program
  signature : ProgramFunctionSignature
  signatureFound : program.signatures.functions.find? (fun s => s.name == "accepted") = some signature
  plan : SourceSpecializationWorklist.Plan
  worklist : SourceSpecializationWorklist.run program [⟨signature.id, []⟩] 64 = .ok (.complete plan)
  compiled : SourceCoreUnifiedCompilation.Compiled
  compiledAccepted : SourceCoreUnifiedCompilation.prepare program plan 500 = .ok compiled
  named : Named
  namedSelected : compiled.indexed.base.functions[0]? = some named
  namedKey : named.signature.key = ⟨signature.id, []⟩
  diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)
  diagnosticsFound : compiled.indexed.base.diagnostics = some diagnostics
  namedCode : Expr
  namedCompiled : namedAction compiled named diagnostics = .ok namedCode
  cached : compiled.indexed.secondPass.closures[0]? = some namedCode

/-- The original finite named producer supplies its real body callback and
parameter/hook receipts from the retained actual compiler equation. -/
theorem Packet.named_compilation (packet : Packet) :
    Nonempty (Compilation packet.compiled.indexed packet.named
      (effectiveDiagnostics packet.compiled packet.diagnostics) packet.namedCode) :=
  CallableIndexedNamedGeneration.of_accepted packet.compiled.indexed packet.namedCompiled

theorem Packet.named_record (packet : Packet) :
    SourceCompilationPlan.exactSpecialization packet.compiled.indexed.base.plan packet.named.signature.key =
      .ok packet.named.specialized := by
  obtain ⟨compilation⟩ := packet.named_compilation
  exact CallableIndexedActualNamedSourceReceipts.cached_record packet.compiled
    packet.namedSelected compilation.hook

/-- Each branch retains its successful equation alongside the returned value. -/
def prepare : Except String Packet := do
  let checked ← match accepted : checkProgram workspace with
    | .error errors => throw s!"checkProgram: {reprStr errors}"
    | .ok program => pure (⟨program, accepted⟩ : {p // checkProgram workspace = .ok p})
  let signature ← match found : checked.val.signatures.functions.find? (fun s => s.name == "accepted") with
    | none => throw "accepted signature missing"
    | some signature => pure (⟨signature, found⟩ : {s // checked.val.signatures.functions.find? (fun s => s.name == "accepted") = some s})
  let plan ← match accepted : SourceSpecializationWorklist.run checked.val [⟨signature.val.id, []⟩] 64 with
    | .ok (.complete plan) => pure (⟨plan, accepted⟩ : {p // SourceSpecializationWorklist.run checked.val [⟨signature.val.id, []⟩] 64 = .ok (.complete p)})
    | other => throw s!"worklist: {reprStr other}"
  let compiled ← match accepted : SourceCoreUnifiedCompilation.prepare checked.val plan.val 500 with
    | .error error => throw s!"unified preparation: {reprStr error}"
    | .ok compiled => pure (⟨compiled, accepted⟩ : {c // SourceCoreUnifiedCompilation.prepare checked.val plan.val 500 = .ok c})
  let named ← match selected : compiled.val.indexed.base.functions[0]? with
    | none => throw "actual named slot missing"
    | some named => pure (⟨named, selected⟩ : {n // compiled.val.indexed.base.functions[0]? = some n})
  if sameKey : named.val.signature.key = ⟨signature.val.id, []⟩ then
    let diagnostics ← match found : compiled.val.indexed.base.diagnostics with
      | none => throw "actual diagnostics missing"
      | some diagnostics => pure (⟨diagnostics, found⟩ : {d // compiled.val.indexed.base.diagnostics = some d})
    let code ← match accepted : namedAction compiled.val named.val diagnostics.val with
      | .error error => throw s!"actual named compilation: {reprStr error}"
      | .ok code => pure (⟨code, accepted⟩ : {c // namedAction compiled.val named.val diagnostics.val = .ok c})
    if cached : compiled.val.indexed.secondPass.closures[0]? = some code.val then
      pure ⟨checked.val, checked.property, signature.val, signature.property, plan.val, plan.property,
        compiled.val, compiled.property, named.val, named.property, sameKey, diagnostics.val,
        diagnostics.property, code.val, code.property, cached⟩
    else throw "actual second-pass cached code disagrees"
  else throw "actual named slot has different specialization key"

def expressionId (packet : Packet) (index : Nat) : ExpressionId :=
  ⟨⟨(source packet.named).owner, index⟩⟩

def statementId (packet : Packet) (index : Nat) : StatementId :=
  ⟨⟨(source packet.named).owner, index⟩⟩

def wordType : TypeSystem.Ty := .constructor (.builtin .word)

def parameterType : TypeSystem.Ty := .product wordType wordType

def indirectMetadata : IndirectCallResolution := {
  argumentCount := 1, argumentTypeBeforeCoercion := parameterType,
  argumentTypeAfterCoercion := parameterType, argumentCoercions := [] }

def literalResolution : IntegerLiteralResolution := {
  rawValue := 7, targetType := wordType, requirement := ⟨0⟩ }

/-- The actual Source rows, including the integer's real requirement ledger.
The outer parent and selected body share this Source but have different ids. -/
structure Graph (packet : Packet) where
  binder : TypedBinder
  parameters : List TypedBinder
  lambdaNode : ExpressionNode
  lambdaFound : (source packet.named).lookupExpression? (expressionId packet 1) = some lambdaNode
  lambdaForm : lambdaNode.form = .lambda parameters wordType [statementId packet 2]
  lambdaType : lambdaNode.type = .function parameterType wordType
  lambdaRequirements : lambdaNode.requirements = []
  lambdaCoercions : lambdaNode.coercions = []
  initialized : StatementNode
  initializedFound : (source packet.named).lookupStatement? (statementId packet 0) = some initialized
  initializedForm : initialized.form = .letDecl binder (some (expressionId packet 1))
  returned : StatementNode
  returnedFound : (source packet.named).lookupStatement? (statementId packet 2) = some returned
  returnedForm : returned.form = .returnStmt (some (expressionId packet 3))
  literal : ExpressionNode
  literalFound : (source packet.named).lookupExpression? (expressionId packet 3) = some literal
  literalForm : literal.form = .integerLiteral (.decimal "7") literalResolution
  literalType : literal.type = wordType
  literalRequirements : literal.requirements = [⟨0⟩]
  literalCoercions : literal.coercions = []
  literalOwned : SourceCompilationPlan.ordinaryOwnedRequirements? literal = some [⟨0⟩]
  parent : ExpressionNode
  parentFound : (source packet.named).lookupExpression? (expressionId packet 5) = some parent
  parentForm : parent.form = .call (expressionId packet 9) [expressionId packet 6] (.indirect indirectMetadata)
  parentType : parent.type = wordType
  parentRequirements : parent.requirements = []
  parentCoercions : parent.coercions = []
  callee : ExpressionNode
  calleeFound : (source packet.named).lookupExpression? (expressionId packet 9) = some callee
  calleeForm : callee.form = .reference "f" (.local binder.id)
  argument : ExpressionNode
  argumentFound : (source packet.named).lookupExpression? (expressionId packet 6) = some argument
  argumentForm : argument.form = .tuple [expressionId packet 7, expressionId packet 8]
  outerReturn : StatementNode
  outerReturnFound : (source packet.named).lookupStatement? (statementId packet 4) = some outerReturn
  outerReturnForm : outerReturn.form = .returnStmt (some (expressionId packet 5))
  roots : (source packet.named).roots = [.statement (statementId packet 0), .statement (statementId packet 4)]

private def expressionAt (packet : Packet) (index : Nat) :
    Except String {node // (source packet.named).lookupExpression? (expressionId packet index) = some node} :=
  match _found : (source packet.named).lookupExpression? (expressionId packet index) with
  | none => .error s!"actual expression {index} missing"
  | some node => .ok ⟨node, rfl⟩

private def statementAt (packet : Packet) (index : Nat) :
    Except String {node // (source packet.named).lookupStatement? (statementId packet index) = some node} :=
  match _found : (source packet.named).lookupStatement? (statementId packet index) with
  | none => .error s!"actual statement {index} missing"
  | some node => .ok ⟨node, rfl⟩

/-- Successful checks return the exact lookup and form equations, without
replacing any typed node, requirement, scope, or compiler expression. -/
def graph (packet : Packet) : Except String (Graph packet) := do
  let lambdaNode ← expressionAt packet 1
  let initialized ← statementAt packet 0
  let returned ← statementAt packet 2
  let literal ← expressionAt packet 3
  let parent ← expressionAt packet 5
  let callee ← expressionAt packet 9
  let argument ← expressionAt packet 6
  let outerReturn ← statementAt packet 4
  match lambdaShape : lambdaNode.val.form, initializedShape : initialized.val.form with
  | .lambda parameters result body, .letDecl binder initializer =>
    if correct : result = wordType ∧ body = [statementId packet 2] ∧
        initializer = some (expressionId packet 1) ∧
        lambdaNode.val.type = .function parameterType wordType ∧
        lambdaNode.val.requirements = [] ∧ lambdaNode.val.coercions = [] ∧
        returned.val.form = .returnStmt (some (expressionId packet 3)) ∧
        literal.val.form = .integerLiteral (.decimal "7") literalResolution ∧
        literal.val.type = wordType ∧ literal.val.requirements = [⟨0⟩] ∧ literal.val.coercions = [] ∧
        SourceCompilationPlan.ordinaryOwnedRequirements? literal.val = some [⟨0⟩] ∧
        parent.val.form = .call (expressionId packet 9) [expressionId packet 6] (.indirect indirectMetadata) ∧
        parent.val.type = wordType ∧ parent.val.requirements = [] ∧ parent.val.coercions = [] ∧
        callee.val.form = .reference "f" (.local binder.id) ∧
        argument.val.form = .tuple [expressionId packet 7, expressionId packet 8] ∧
        outerReturn.val.form = .returnStmt (some (expressionId packet 5)) ∧
        (source packet.named).roots = [.statement (statementId packet 0), .statement (statementId packet 4)] then
      have ⟨sameResult, sameBody, sameInitializer, lambdaType, lambdaRequirements, lambdaCoercions,
        returnedForm, literalForm, literalType, literalRequirements, literalCoercions, literalOwned,
        parentForm, parentType, parentRequirements, parentCoercions, calleeForm, argumentForm,
        outerReturnForm, roots⟩ := correct
      pure ⟨binder, parameters, lambdaNode.val, lambdaNode.property,
        by simpa only [sameResult, sameBody] using lambdaShape,
        lambdaType, lambdaRequirements, lambdaCoercions, initialized.val, initialized.property,
        by simpa only [sameInitializer] using initializedShape,
        returned.val, returned.property, returnedForm, literal.val, literal.property,
        literalForm, literalType, literalRequirements, literalCoercions, literalOwned,
        parent.val, parent.property, parentForm, parentType, parentRequirements, parentCoercions,
        callee.val, callee.property, calleeForm, argument.val, argument.property, argumentForm,
        outerReturn.val, outerReturn.property, outerReturnForm, roots⟩
    else throw "actual Source graph differs from the written fixture"
  | _, _ => throw "actual initializer/lambda forms differ from the written fixture"

/-- The real approved literal body domain permits the external indirect call
in this same Source. This proof needs neither a runtime classification nor a
completed body meaning. -/
theorem Graph.body_no_indirect {packet : Packet} (given : Graph packet) :
    CallableIndexedOwnedPreparedMixedBodyRuntimeBounds.NoIndirectOn (source packet.named)
      (fun id => id = expressionId packet 3) := by
  intro id node callee ids metadata allowed found
  subst id
  have same : node = given.literal := Option.some.inj (found.symm.trans given.literalFound)
  subst node
  rw [given.literalForm]
  intro impossible
  cases impossible

theorem Graph.parent_outside_body {packet : Packet} (_given : Graph packet) :
    expressionId packet 5 ≠ expressionId packet 3 := by
  intro same
  have indices := congrArg (fun id : ExpressionId => id.occurrence.index) same
  cases indices

theorem Graph.whole_source_has_indirect {packet : Packet} (given : Graph packet) :
    ¬ CallableIndexedOwnedPreparedMixedBodyRuntimeBounds.NoIndirect (source packet.named) := by
  intro excluded
  exact excluded given.parentFound given.parentForm

def initialScope (packet : Packet) : SourceCoreLocalCell.Scope :=
  packet.named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))

def parentContexts (packet : Packet) :=
  SourceCoreStageCodebook.prepareContexts packet.compiled.indexed.base.sourceProgram
    packet.compiled.indexed.base.plan (packet.compiled.indexed.base.locals.bindings.flatMap (·.instances))

def contextualAction (packet : Packet) (parents : List SourceCoreLocalEvidence.Prepared)
    (own : SourceCoreProgramFaultSites.Function) (fuel : Nat) (scope : SourceCoreLocalCell.Scope)
    (id : ExpressionId) :=
  SourceCoreGeneralFunctions.lowerContextualExpression packet.compiled.indexed.base.sourceProgram
    ((representation packet.compiled.indexed).atContext packet.named.signature.key [])
    packet.compiled.indexed.base.sourceProgram.signatures packet.compiled.indexed.base.locals
    parents own.assignments (effectiveDiagnostics packet.compiled packet.diagnostics)
    (context packet.compiled.indexed packet.named) packet.compiled.indexed.base.callableContext none none
    fuel (source packet.named) scope id
    ((effectiveDiagnostics packet.compiled packet.diagnostics).reasonAt packet.named.signature.key)

def binderAction (packet : Packet) (given : Graph packet) :=
  SourceCoreGeneralFunctions.contextualBinder
    ((representation packet.compiled.indexed).atContext packet.named.signature.key [])
    packet.compiled.indexed.base.locals packet.named.signature.key []
    (source packet.named) (initialScope packet) given.binder

/-- The original contextual calls at the actual named body's two child
budgets. These equations do not identify their separately selected policies. -/
structure CompilerCalls (packet : Packet) (given : Graph packet) where
  fuel : packet.compiled.indexed.fuel = 500
  parents : List SourceCoreLocalEvidence.Prepared
  parentsPrepared : parentContexts packet = .ok parents
  own : SourceCoreProgramFaultSites.Function
  ownFound : (effectiveDiagnostics packet.compiled packet.diagnostics).base.find? packet.named.signature.key = some own
  payload : Ty
  binderPrepared : binderAction packet given = .ok payload
  initializedRead : SourceCoreCompatibleDataExpressions.readStatement packet.compiled.compatible.checked
    (source packet.named) (statementId packet 0) = .ok (given.initialized, .unit)
  returnedRead : SourceCoreCompatibleDataExpressions.readStatement packet.compiled.compatible.checked
    (source packet.named) (statementId packet 4) = .ok (given.outerReturn, packet.named.signature.resultType)
  initializer : SourceCoreBasic.LoweredExpr
  initializerCompiled : contextualAction packet parents own 499 (initialScope packet) (expressionId packet 1) = .ok initializer
  parent : SourceCoreBasic.LoweredExpr
  parentCompiled : contextualAction packet parents own 498
    ((given.binder.id, payload) :: initialScope packet) (expressionId packet 5) = .ok parent
  body : Expr
  bodyCompiled : bodyAction packet.compiled.indexed packet.named
    (effectiveDiagnostics packet.compiled packet.diagnostics) parents own
    [statementId packet 0, statementId packet 4] = .ok body
  literalOrdinary : packet.compiled.indexed.base.locals.bindings.find? (fun binding =>
    decide (binding.caller = packet.named.signature.key ∧ binding.initializer = expressionId packet 3)) = none
  lambdaOrdinary : packet.compiled.indexed.base.locals.bindings.find? (fun binding =>
    decide (binding.caller = packet.named.signature.key ∧ binding.initializer = expressionId packet 1)) = none
  parentOrdinary : packet.compiled.indexed.base.locals.bindings.find? (fun binding =>
    decide (binding.caller = packet.named.signature.key ∧ binding.initializer = expressionId packet 5)) = none

private def readStatementAt (packet : Packet) (id : StatementId) (node : StatementNode) (type : Ty) :
    Except String (PLift (SourceCoreCompatibleDataExpressions.readStatement packet.compiled.compatible.checked
      (source packet.named) id = .ok (node, type))) :=
  match _accepted : SourceCoreCompatibleDataExpressions.readStatement packet.compiled.compatible.checked
      (source packet.named) id with
  | .error error => .error s!"actual statement read: {reprStr error}"
  | .ok actual =>
    if same : actual = (node, type) then .ok ⟨congrArg Except.ok same⟩
    else .error "actual statement read differs"

private def ordinaryAt (packet : Packet) (id : ExpressionId) :
    Except String (PLift (packet.compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = packet.named.signature.key ∧ binding.initializer = id)) = none)) :=
  match found : packet.compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = packet.named.signature.key ∧ binding.initializer = id)) with
  | none => .ok ⟨found⟩
  | some _ => .error "actual initialized generalized-local entry is present"

def compilerCalls (packet : Packet) (given : Graph packet) : Except String (CompilerCalls packet given) := do
  let parents ← match accepted : parentContexts packet with
    | .error error => throw s!"actual parent contexts: {reprStr error}"
    | .ok parents => pure (⟨parents, accepted⟩ : {p // parentContexts packet = .ok p})
  let own ← match found : (effectiveDiagnostics packet.compiled packet.diagnostics).base.find? packet.named.signature.key with
    | none => throw "actual owning diagnostics missing"
    | some own => pure (⟨own, found⟩ : {o // (effectiveDiagnostics packet.compiled packet.diagnostics).base.find? packet.named.signature.key = some o})
  let payload ← match accepted : binderAction packet given with
    | .error error => throw s!"actual contextual binder: {reprStr error}"
    | .ok type => pure (⟨type, accepted⟩ : {t // binderAction packet given = .ok t})
  let initializer ← match accepted : contextualAction packet parents.val own.val 499 (initialScope packet) (expressionId packet 1) with
    | .error error => throw s!"actual lambda initializer: {reprStr error}"
    | .ok lowered => pure (⟨lowered, accepted⟩ : {l // contextualAction packet parents.val own.val 499 (initialScope packet) (expressionId packet 1) = .ok l})
  let parent ← match accepted : contextualAction packet parents.val own.val 498
      ((given.binder.id, payload.val) :: initialScope packet) (expressionId packet 5) with
    | .error error => throw s!"actual indirect parent: {reprStr error}"
    | .ok lowered => pure (⟨lowered, accepted⟩ : {l // contextualAction packet parents.val own.val 498 ((given.binder.id, payload.val) :: initialScope packet) (expressionId packet 5) = .ok l})
  let body ← match accepted : bodyAction packet.compiled.indexed packet.named
      (effectiveDiagnostics packet.compiled packet.diagnostics) parents.val own.val
      [statementId packet 0, statementId packet 4] with
    | .error error => throw s!"actual named body: {reprStr error}"
    | .ok body => pure (⟨body, accepted⟩ : {b // bodyAction packet.compiled.indexed packet.named (effectiveDiagnostics packet.compiled packet.diagnostics) parents.val own.val [statementId packet 0, statementId packet 4] = .ok b})
  let initializedRead ← readStatementAt packet (statementId packet 0) given.initialized .unit
  let returnedRead ← readStatementAt packet (statementId packet 4) given.outerReturn packet.named.signature.resultType
  let literalOrdinary ← ordinaryAt packet (expressionId packet 3)
  let lambdaOrdinary ← ordinaryAt packet (expressionId packet 1)
  let parentOrdinary ← ordinaryAt packet (expressionId packet 5)
  if fuel : packet.compiled.indexed.fuel = 500 then
    pure ⟨fuel, parents.val, parents.property, own.val, own.property, payload.val, payload.property,
      initializedRead.down, returnedRead.down, initializer.val, initializer.property, parent.val, parent.property,
      body.val, body.property, literalOrdinary.down, lambdaOrdinary.down, parentOrdinary.down⟩
  else throw "actual contextual fuel/read/ordinary receipts differ"

/-- These are the same parent context, owning row, statements, and body as
every Compilation supplied by the original accepted named producer. -/
theorem CompilerCalls.compilation_alignment {packet : Packet} {given : Graph packet}
    (calls : CompilerCalls packet given)
    (compilation : Compilation packet.compiled.indexed packet.named
      (effectiveDiagnostics packet.compiled packet.diagnostics) packet.namedCode) :
    compilation.parents = calls.parents ∧ compilation.own = calls.own ∧
      compilation.statements = [statementId packet 0, statementId packet 4] ∧
      compilation.body = calls.body := by
  have parents : compilation.parents = calls.parents := Except.ok.inj
    (compilation.parentsPrepared.symm.trans calls.parentsPrepared)
  have own : compilation.own = calls.own := Option.some.inj
    (compilation.diagnostic.symm.trans calls.ownFound)
  have roots : compilation.statements = [statementId packet 0, statementId packet 4] := by
    have found := compilation.roots
    rw [given.roots] at found
    simpa only [List.mapM_cons, List.mapM_nil, pure, Except.pure, bind, Except.bind,
      Except.ok.injEq] using found.symm
  have body := compilation.bodyCompiled
  rw [parents, own, roots] at body
  exact ⟨parents, own, roots, Except.ok.inj (body.symm.trans calls.bodyCompiled)⟩

structure NamedTail (packet : Packet) {given : Graph packet} (calls : CompilerCalls packet given) where
  parameters : Expr
  parametersCompiled : SourceCoreSourceCells.bindParameters
    (allocator packet.compiled.indexed packet.named) (source packet.named) [] packet.named.inputs
    packet.named.signature.resultType SourceCoreFunctions.argumentProjection calls.body = .ok parameters
  output : Expr
  hook : SourceCoreCallableIndexedAncestry.namedBody packet.compiled.indexed.ancestry
    packet.named parameters = .ok output
  emitted : packet.namedCode = .lambda packet.named.signature.parameterType
    (LanguageResult.resultType packet.named.signature.resultType) output

/-- Retain the real parameter installation and named hook as computable data.
The sealed Compilation still comes from its original accepted producer. -/
def namedTail (packet : Packet) {given : Graph packet} (calls : CompilerCalls packet given) :
    Except String (NamedTail packet calls) := do
  let parameters ← match accepted : SourceCoreSourceCells.bindParameters
      (allocator packet.compiled.indexed packet.named) (source packet.named) [] packet.named.inputs
      packet.named.signature.resultType SourceCoreFunctions.argumentProjection calls.body with
    | .error error => throw s!"actual named parameter installation: {reprStr error}"
    | .ok parameters => pure (⟨parameters, accepted⟩ : {p // SourceCoreSourceCells.bindParameters
        (allocator packet.compiled.indexed packet.named) (source packet.named) [] packet.named.inputs
        packet.named.signature.resultType SourceCoreFunctions.argumentProjection calls.body = .ok p})
  let output ← match accepted : SourceCoreCallableIndexedAncestry.namedBody packet.compiled.indexed.ancestry
      packet.named parameters.val with
    | .error error => throw s!"actual named hook: {reprStr error}"
    | .ok output => pure (⟨output, accepted⟩ : {o // SourceCoreCallableIndexedAncestry.namedBody
        packet.compiled.indexed.ancestry packet.named parameters.val = .ok o})
  if emitted : packet.namedCode = .lambda packet.named.signature.parameterType
      (LanguageResult.resultType packet.named.signature.resultType) output.val then
    pure ⟨parameters.val, parameters.property, output.val, output.property, emitted⟩
  else throw "actual named hook emission disagrees with cached compiler output"

theorem NamedTail.compilation_alignment {packet : Packet} {given : Graph packet}
    {calls : CompilerCalls packet given} (tail : NamedTail packet calls)
    (compilation : Compilation packet.compiled.indexed packet.named
      (effectiveDiagnostics packet.compiled packet.diagnostics) packet.namedCode) :
    compilation.parameterCode = tail.parameters ∧ compilation.output = tail.output := by
  have body := (calls.compilation_alignment compilation).2.2.2
  have prepared := compilation.parametersCompiled
  rw [body] at prepared
  have parameters := Except.ok.inj (prepared.symm.trans tail.parametersCompiled)
  have hook := compilation.hook
  rw [parameters] at hook
  exact ⟨parameters, Except.ok.inj (hook.symm.trans tail.hook)⟩

def wordRequirement (index : Nat) : SolvedRequirement := {
  id := ⟨index⟩, predicate := ProgramSignatures.builtinIntPredicate wordType,
  evidence := .implementation (.byImpl (ProgramSignatures.builtinIntPredicate wordType) (.builtin .intWord) []) }

def numericRows : List SolvedRequirement := [wordRequirement 0, wordRequirement 1, wordRequirement 2]

private def numericRow (index : Nat) (row : SolvedRequirement) :
    Except String (PLift (row = wordRequirement index)) :=
  match row with
  | ⟨id, predicate, .implementation (.byImpl goal (.builtin .intWord) [])⟩ =>
    if correct : id = ⟨index⟩ ∧ predicate = ProgramSignatures.builtinIntPredicate wordType ∧
        goal = ProgramSignatures.builtinIntPredicate wordType then
      .ok ⟨by obtain ⟨rfl, rfl, rfl⟩ := correct; rfl⟩
    else .error "actual numeric row id/predicate differs"
  | _ => .error "actual numeric row does not retain the intrinsic Word implementation"

/-- Inspect the real constructors, not a Boolean equality assumed lawful for
the evidence carrier. All stable numeric ids and implementation trees survive. -/
def numericLedger (packet : Packet) :
    Except String (PLift (packet.named.specialized.function.solvedRequirements = numericRows)) :=
  match _rows : packet.named.specialized.function.solvedRequirements with
  | [first, second, third] => do
    let firstEq ← numericRow 0 first
    let secondEq ← numericRow 1 second
    let thirdEq ← numericRow 2 third
    pure ⟨by simp only [firstEq.down, secondEq.down, thirdEq.down, numericRows]⟩
  | _ => .error "actual numeric ledger does not contain the three written literals"

/-- Intrinsic numeric evidence is independently valid in the real catalog. -/
theorem wordRequirement_valid (context : SourceSemantics.Context) (index : Nat) :
    SolvedRequirementValid context (wordRequirement index) := by
  apply SolvedRequirementValid.intro
  apply RetainedEvidenceValid.intro
    (.implementation (.byImpl .nil))
  apply EvidenceValid.implementation (rule := ProgramSignatures.builtinIntWordRule)
  · simp [ProgramSignatures.resolutionRules, ProgramSignatures.builtinResolutionRules]
  · rfl
  · apply ImplHeadInstantiates.intro ⟨[], []⟩
    · constructor
      · change ParameterSubstitution.Exact [] []
        exact ⟨List.nodup_nil, List.Perm.refl []⟩
      · change ExactSubstitution [] []
        exact ExactSubstitution.empty
    · rfl
    · rfl
  · exact .nil

theorem numeric_requirement {context : SourceSemantics.Context}
    (rows : context.solvedRequirements = numericRows) {index : Nat}
    (member : index = 0 ∨ index = 1 ∨ index = 2) :
    RequirementProves context ⟨index⟩ (ProgramSignatures.builtinIntPredicate wordType) := by
  refine ⟨wordRequirement index, ⟨?_, rfl⟩, rfl, wordRequirement_valid context index⟩
  rw [rows]
  rcases member with rfl | rfl | rfl <;> simp [numericRows]

theorem numeric_runtime_ledger {context : SourceSemantics.Context}
    (rows : context.solvedRequirements = numericRows) : RuntimeRequirementLedgerValid context := by
  refine ⟨?_, ?_⟩
  · simp [RequirementIdsUnique, rows, numericRows, wordRequirement]
  · intro row evidence member _sameEvidence
    rw [rows] at member
    simp only [numericRows, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> exact wordRequirement_valid context _

def argumentResolution (value requirement : Nat) : IntegerLiteralResolution :=
  ⟨value, wordType, ⟨requirement⟩⟩

/-- These are the original local read, tuple, and numeric child rows used by
the accepted parent. Their override exclusions are checked at the actual catalog. -/
structure ParentRows (packet : Packet) (given : Graph packet) where
  left : ExpressionNode
  leftFound : (source packet.named).lookupExpression? (expressionId packet 7) = some left
  leftForm : left.form = .integerLiteral (.decimal "1") (argumentResolution 1 1)
  leftCoercions : left.coercions = []
  leftOwned : SourceCompilationPlan.ordinaryOwnedRequirements? left = some [⟨1⟩]
  right : ExpressionNode
  rightFound : (source packet.named).lookupExpression? (expressionId packet 8) = some right
  rightForm : right.form = .integerLiteral (.decimal "2") (argumentResolution 2 2)
  rightCoercions : right.coercions = []
  rightOwned : SourceCompilationPlan.ordinaryOwnedRequirements? right = some [⟨2⟩]
  calleeRequirements : given.callee.requirements = []
  calleeCoercions : given.callee.coercions = []
  argumentRequirements : given.argument.requirements = []
  argumentCoercions : given.argument.coercions = []
  generalized : packet.compiled.indexed.base.locals.bindings.any (fun binding =>
    decide (binding.caller = packet.named.signature.key ∧ binding.binder.id = given.binder.id)) = false
  leftOrdinary : packet.compiled.indexed.base.locals.bindings.find? (fun binding =>
    decide (binding.caller = packet.named.signature.key ∧ binding.initializer = expressionId packet 7)) = none
  rightOrdinary : packet.compiled.indexed.base.locals.bindings.find? (fun binding =>
    decide (binding.caller = packet.named.signature.key ∧ binding.initializer = expressionId packet 8)) = none
  calleeOrdinary : packet.compiled.indexed.base.locals.bindings.find? (fun binding =>
    decide (binding.caller = packet.named.signature.key ∧ binding.initializer = expressionId packet 9)) = none
  argumentOrdinary : packet.compiled.indexed.base.locals.bindings.find? (fun binding =>
    decide (binding.caller = packet.named.signature.key ∧ binding.initializer = expressionId packet 6)) = none
  calleeCore : Ty
  calleeRead : SourceCoreCompatibleDataExpressions.readExpression packet.compiled.compatible.checked
    (source packet.named) (expressionId packet 9) = .ok (given.callee, calleeCore)
  argumentCore : Ty
  argumentRead : SourceCoreCompatibleDataExpressions.readExpression packet.compiled.compatible.checked
    (source packet.named) (expressionId packet 6) = .ok (given.argument, argumentCore)
  parentCore : Ty
  parentRead : SourceCoreCompatibleDataExpressions.readExpression packet.compiled.compatible.checked
    (source packet.named) (expressionId packet 5) = .ok (given.parent, parentCore)

private def expressionReadAt (packet : Packet) (id : ExpressionId) (node : ExpressionNode) :
    Except String {type // SourceCoreCompatibleDataExpressions.readExpression packet.compiled.compatible.checked
      (source packet.named) id = .ok (node, type)} :=
  match _accepted : SourceCoreCompatibleDataExpressions.readExpression packet.compiled.compatible.checked
      (source packet.named) id with
  | .error error => .error s!"actual expression read: {reprStr error}"
  | .ok (actual, type) =>
    if same : actual = node then .ok ⟨type, same ▸ rfl⟩
    else .error "actual expression read selected another row"

def parentRows (packet : Packet) (given : Graph packet) : Except String (ParentRows packet given) := do
  let left ← expressionAt packet 7
  let right ← expressionAt packet 8
  let leftOrdinary ← ordinaryAt packet (expressionId packet 7)
  let rightOrdinary ← ordinaryAt packet (expressionId packet 8)
  let calleeOrdinary ← ordinaryAt packet (expressionId packet 9)
  let argumentOrdinary ← ordinaryAt packet (expressionId packet 6)
  let calleeRead ← expressionReadAt packet (expressionId packet 9) given.callee
  let argumentRead ← expressionReadAt packet (expressionId packet 6) given.argument
  let parentRead ← expressionReadAt packet (expressionId packet 5) given.parent
  if correct : left.val.form = .integerLiteral (.decimal "1") (argumentResolution 1 1) ∧
      left.val.coercions = [] ∧ SourceCompilationPlan.ordinaryOwnedRequirements? left.val = some [⟨1⟩] ∧
      right.val.form = .integerLiteral (.decimal "2") (argumentResolution 2 2) ∧
      right.val.coercions = [] ∧ SourceCompilationPlan.ordinaryOwnedRequirements? right.val = some [⟨2⟩] ∧
      given.callee.requirements = [] ∧ given.callee.coercions = [] ∧
      given.argument.requirements = [] ∧ given.argument.coercions = [] ∧
      packet.compiled.indexed.base.locals.bindings.any (fun binding =>
        decide (binding.caller = packet.named.signature.key ∧ binding.binder.id = given.binder.id)) = false then
    have ⟨leftForm, leftCoercions, leftOwned, rightForm, rightCoercions, rightOwned,
      calleeRequirements, calleeCoercions, argumentRequirements, argumentCoercions, generalized⟩ := correct
    pure ⟨left.val, left.property, leftForm, leftCoercions, leftOwned,
      right.val, right.property, rightForm, rightCoercions, rightOwned,
      calleeRequirements, calleeCoercions, argumentRequirements, argumentCoercions, generalized,
      leftOrdinary.down, rightOrdinary.down, calleeOrdinary.down, argumentOrdinary.down,
      calleeRead.val, calleeRead.property, argumentRead.val, argumentRead.property, parentRead.val, parentRead.property⟩
  else throw "actual parent child override metadata differs"

/-- This finite compiler check uses the original compatible fields. It is
compared pointwise with the one selected initializer policy below. -/
def ordinaryPolicy (packet : Packet) : SourceCoreFunctions.Policy := {
  ((representation packet.compiled.indexed).atContext packet.named.signature.key []).expressions with
  callables := SourceCoreGeneralFunctions.callablePolicy packet.compiled.indexed.base.callableContext []
  readExpression := SourceCoreCompatibleDataExpressions.readExpression packet.compiled.compatible.checked
  lowerSpecial? := none }

def ordinaryBody (packet : Packet) {given : Graph packet} (calls : CompilerCalls packet given) :
    SourceCoreFunctions.BodyLowerer :=
  SourceCoreGeneralFunctions.bodyLowererWithRepresentation
    ((representation packet.compiled.indexed).atContext packet.named.signature.key [])
    (context packet.compiled.indexed packet.named).solvedRequirements calls.own.assignments
    (effectiveDiagnostics packet.compiled packet.diagnostics) packet.named.signature.key
    (SourceCoreGeneralFunctions.contextualBinder
      ((representation packet.compiled.indexed).atContext packet.named.signature.key [])
      packet.compiled.indexed.base.locals packet.named.signature.key [])

def ordinaryParentAction (packet : Packet) {given : Graph packet} (calls : CompilerCalls packet given) :=
  SourceCoreFunctions.lowerExpressionWithPolicy (ordinaryPolicy packet) (ordinaryBody packet calls) 498
    (context packet.compiled.indexed packet.named) (source packet.named)
    ((given.binder.id, calls.payload) :: initialScope packet) (expressionId packet 5)
    ((effectiveDiagnostics packet.compiled packet.diagnostics).reasonAt packet.named.signature.key)

def ordinaryParent (packet : Packet) {given : Graph packet} (calls : CompilerCalls packet given) :
    Except String (PLift (ordinaryParentAction packet calls = .ok calls.parent)) :=
  match _accepted : ordinaryParentAction packet calls with
  | .error error => .error s!"same compatible parent action: {reprStr error}"
  | .ok lowered => if same : lowered = calls.parent then .ok ⟨congrArg Except.ok same⟩
    else .error "same compatible parent action changed the original emitted output"

private abbrev SpecialNone (policy : SourceCoreFunctions.Policy)
    (context : SourceCoreFunctions.Context) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (reasonAt : ExpressionId → Word) :=
  ∀ child budget, (match policy.lowerSpecial? with
    | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
    | some lower => lower context child budget source scope id reasonAt) = .ok none

private theorem integer_branch_same
    {first second : SourceCoreFunctions.Policy} {firstBody secondBody : SourceCoreFunctions.BodyLowerer}
    {context : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {reasonAt : ExpressionId → Word} {node : ExpressionNode}
    {literal : Syntax.CoreLiteralValue} {resolution : IntegerLiteralResolution}
    (fuel : Nat) (owner : id.occurrence.owner = source.owner)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .integerLiteral literal resolution)
    (firstSpecial : SpecialNone first context source scope id reasonAt)
    (secondSpecial : SpecialNone second context source scope id reasonAt) :
    SourceCoreFunctions.lowerExpressionWithPolicy first firstBody (fuel + 1) context source scope id reasonAt =
      SourceCoreFunctions.lowerExpressionWithPolicy second secondBody (fuel + 1) context source scope id reasonAt := by
  conv => lhs; rw [SourceCoreFunctions.lowerExpressionWithPolicy.eq_def]
  conv => rhs; rw [SourceCoreFunctions.lowerExpressionWithPolicy.eq_def]
  cases firstChoice : first.lowerSpecial? <;> cases secondChoice : second.lowerSpecial?
  all_goals
    simp only [SpecialNone, firstChoice] at firstSpecial
    simp only [SpecialNone, secondChoice] at secondSpecial
    simp_all only [ne_eq, not_true_eq_false, ↓reduceIte, pure, Except.pure, bind, Except.bind]

private theorem reference_branch_same
    {first second : SourceCoreFunctions.Policy} {firstBody secondBody : SourceCoreFunctions.BodyLowerer}
    {context : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {reasonAt : ExpressionId → Word} {node : ExpressionNode}
    {name : String} {binder : Resolved.LocalId} {type : Ty}
    (fuel : Nat) (owner : id.occurrence.owner = source.owner)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .reference name (.local binder))
    (firstSpecial : SpecialNone first context source scope id reasonAt)
    (secondSpecial : SpecialNone second context source scope id reasonAt)
    (firstRead : first.readExpression source id = .ok (node, type))
    (secondRead : second.readExpression source id = .ok (node, type))
    (read : first.lowerRead = second.lowerRead) :
    SourceCoreFunctions.lowerExpressionWithPolicy first firstBody (fuel + 1) context source scope id reasonAt =
      SourceCoreFunctions.lowerExpressionWithPolicy second secondBody (fuel + 1) context source scope id reasonAt := by
  conv => lhs; rw [SourceCoreFunctions.lowerExpressionWithPolicy.eq_def]
  conv => rhs; rw [SourceCoreFunctions.lowerExpressionWithPolicy.eq_def]
  cases firstChoice : first.lowerSpecial? <;> cases secondChoice : second.lowerSpecial?
  all_goals
    simp only [SpecialNone, firstChoice] at firstSpecial
    simp only [SpecialNone, secondChoice] at secondSpecial
    simp_all only [ne_eq, not_true_eq_false, ↓reduceIte, pure, Except.pure, bind, Except.bind]

private theorem tuple_branch_same
    {first second : SourceCoreFunctions.Policy} {firstBody secondBody : SourceCoreFunctions.BodyLowerer}
    {context : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id left right : ExpressionId} {reasonAt : ExpressionId → Word} {node : ExpressionNode} {type : Ty}
    (fuel : Nat) (owner : id.occurrence.owner = source.owner)
    (found : source.lookupExpression? id = some node) (form : node.form = .tuple [left, right])
    (firstSpecial : SpecialNone first context source scope id reasonAt)
    (secondSpecial : SpecialNone second context source scope id reasonAt)
    (firstRead : first.readExpression source id = .ok (node, type))
    (secondRead : second.readExpression source id = .ok (node, type))
    (leftSame : SourceCoreFunctions.lowerExpressionWithPolicy first firstBody fuel context source scope left reasonAt =
      SourceCoreFunctions.lowerExpressionWithPolicy second secondBody fuel context source scope left reasonAt)
    (rightSame : SourceCoreFunctions.lowerExpressionWithPolicy first firstBody fuel context source scope right reasonAt =
      SourceCoreFunctions.lowerExpressionWithPolicy second secondBody fuel context source scope right reasonAt) :
    SourceCoreFunctions.lowerExpressionWithPolicy first firstBody (fuel + 1) context source scope id reasonAt =
      SourceCoreFunctions.lowerExpressionWithPolicy second secondBody (fuel + 1) context source scope id reasonAt := by
  conv => lhs; rw [SourceCoreFunctions.lowerExpressionWithPolicy.eq_def]
  conv => rhs; rw [SourceCoreFunctions.lowerExpressionWithPolicy.eq_def]
  cases firstChoice : first.lowerSpecial? <;> cases secondChoice : second.lowerSpecial?
  all_goals
    simp only [SpecialNone, firstChoice] at firstSpecial
    simp only [SpecialNone, secondChoice] at secondSpecial
    simp_all only [ne_eq, not_true_eq_false, ↓reduceIte, pure, Except.pure, bind, Except.bind]

private theorem indirect_branch_same
    {first second : SourceCoreFunctions.Policy} {firstBody secondBody : SourceCoreFunctions.BodyLowerer}
    {context : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id callee argument : ExpressionId} {reasonAt : ExpressionId → Word} {node : ExpressionNode} {type : Ty}
    {metadata : IndirectCallResolution}
    (fuel : Nat) (owner : id.occurrence.owner = source.owner)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee [argument] (.indirect metadata))
    (firstSpecial : SpecialNone first context source scope id reasonAt)
    (secondSpecial : SpecialNone second context source scope id reasonAt)
    (firstRead : first.readExpression source id = .ok (node, type))
    (secondRead : second.readExpression source id = .ok (node, type))
    (calleeRead : first.readExpression source callee = second.readExpression source callee)
    (project : first.projectType = second.projectType) (callables : first.callables = second.callables)
    (calleeSame : SourceCoreFunctions.lowerExpressionWithPolicy first firstBody fuel context source scope callee reasonAt =
      SourceCoreFunctions.lowerExpressionWithPolicy second secondBody fuel context source scope callee reasonAt)
    (argumentSame : SourceCoreFunctions.lowerExpressionWithPolicy first firstBody fuel context source scope argument reasonAt =
      SourceCoreFunctions.lowerExpressionWithPolicy second secondBody fuel context source scope argument reasonAt) :
    SourceCoreFunctions.lowerExpressionWithPolicy first firstBody (fuel + 1) context source scope id reasonAt =
      SourceCoreFunctions.lowerExpressionWithPolicy second secondBody (fuel + 1) context source scope id reasonAt := by
  conv => lhs; rw [SourceCoreFunctions.lowerExpressionWithPolicy.eq_def]
  conv => rhs; rw [SourceCoreFunctions.lowerExpressionWithPolicy.eq_def]
  cases firstChoice : first.lowerSpecial? <;> cases secondChoice : second.lowerSpecial?
  all_goals
    simp only [SpecialNone, firstChoice] at firstSpecial
    simp only [SpecialNone, secondChoice] at secondSpecial
    simp_all only [ne_eq, not_true_eq_false, ↓reduceIte, pure, Except.pure, bind, Except.bind, List.mapM_cons, List.mapM_nil]

/-- The one initializer selector is evaluated only against the authentic
Compilation. Its accepted action is transported by original callback alignment. -/
def CompilerCalls.initializer_root {packet : Packet} {given : Graph packet}
    (calls : CompilerCalls packet given)
    (compilation : Compilation packet.compiled.indexed packet.named
      (effectiveDiagnostics packet.compiled packet.diagnostics) packet.namedCode) :
    CallableIndexedOwnedLiteralReturnSiteShells.LiteralRootReceipt
      (compiled := packet.compiled) packet.named (effectiveDiagnostics packet.compiled packet.diagnostics)
      packet.namedCode compilation 498 (source packet.named) (initialScope packet) (expressionId packet 1)
      ((effectiveDiagnostics packet.compiled packet.diagnostics).reasonAt packet.named.signature.key)
      calls.initializer := by
  have ⟨parents, own, _statements, _body⟩ := calls.compilation_alignment compilation
  apply CallableIndexedOwnedLiteralReturnSiteShells.LiteralRootReceipt.of_accepted compilation packet.named_record
  simpa only [parents, own, contextualAction] using calls.initializerCompiled

private theorem ordinary_pointwise {packet : Packet}
    {compilation : Compilation packet.compiled.indexed packet.named
      (effectiveDiagnostics packet.compiled packet.diagnostics) packet.namedCode}
    {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {rootLowered : SourceCoreBasic.LoweredExpr}
    (root : CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt
      (compiled := packet.compiled) packet.named (effectiveDiagnostics packet.compiled packet.diagnostics)
      packet.namedCode compilation rootFuel rootSource rootScope rootId
      ((effectiveDiagnostics packet.compiled packet.diagnostics).reasonAt packet.named.signature.key) rootLowered)
    {childScope : SourceCoreLocalCell.Scope} {childId : ExpressionId} {node : ExpressionNode}
    {owned : List RequirementId}
    (found : (source packet.named).lookupExpression? childId = some node)
    (shape : (∃ name binder, node.form = .reference name (.local binder) ∧
        packet.compiled.indexed.base.locals.bindings.any (fun binding =>
          decide (binding.caller = packet.named.signature.key ∧ binding.binder.id = binder)) = false) ∨
      (∃ ids, node.form = .tuple ids) ∨
      (∃ literal resolution, node.form = .integerLiteral literal resolution))
    (ownedRequirements : SourceCompilationPlan.ordinaryOwnedRequirements? node = some owned)
    (coercions : node.coercions = [])
    (requirements : node.requirements = [] ∨ ∃ literal resolution, node.form = .integerLiteral literal resolution)
    (ordinary : packet.compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = packet.named.signature.key ∧ binding.initializer = childId)) = none) :
    CallableIndexedOwnedContextualCompilerPolicyProfiles.PointwiseFor root
      (source packet.named) childScope childId
      ((effectiveDiagnostics packet.compiled packet.diagnostics).reasonAt packet.named.signature.key) := by
  have owner : (context packet.compiled.indexed packet.named).owner = packet.named.signature.key := rfl
  have sameSource : SourceCoreGeneralFunctions.contextualSource packet.compiled.indexed.base.sourceProgram
      (context packet.compiled.indexed packet.named).plan packet.compiled.indexed.base.locals
      (context packet.compiled.indexed packet.named).owner none (source packet.named) childId = .ok (source packet.named) := by
    rcases shape with ⟨name, binder, form, generalized⟩ | ⟨ids, form⟩ | ⟨literal, resolution, form⟩
    · simp only [SourceCoreGeneralFunctions.contextualSource, found, bind, Except.bind, pure, Except.pure, form, owner, generalized, Bool.false_eq_true, ↓reduceIte]
    · simp [SourceCoreGeneralFunctions.contextualSource, found, form]
    · simp [SourceCoreGeneralFunctions.contextualSource, found, form]
  constructor
  · rw [root.selected.readExpression]
    simp only [sameSource, bind, Except.bind]
    rw [CallableIndexedOwnedIndirectCompilerPolicyInputs.representation_read (compiled := packet.compiled) packet.named]
  · intro child budget
    rw [root.selected.special_eq, root.selected.special_body]
    have evidenceNone : SourceCoreEvidence.lowerWithProjector packet.compiled.indexed.base.sourceProgram
        ((representation packet.compiled.indexed).atContext packet.named.signature.key []).expressions.projectType
        packet.named.specialized (context packet.compiled.indexed packet.named) child budget
        (source packet.named) childScope childId
        ((effectiveDiagnostics packet.compiled packet.diagnostics).reasonAt packet.named.signature.key)
        (SourceCoreGeneralFunctions.callablePolicy packet.compiled.indexed.base.callableContext []) = .ok none := by
      rcases requirements with empty | ⟨literal, resolution, form⟩
      · rcases shape with ⟨name, binder, form, _generalized⟩ | ⟨ids, form⟩ | ⟨literal, resolution, form⟩ <;>
          simp [SourceCoreEvidence.lowerWithProjector, found, form, ownedRequirements, coercions, empty]
      · simp [SourceCoreEvidence.lowerWithProjector, found, form, ownedRequirements, coercions]
    simp only [bind, Except.bind]
    rw [sameSource]
    simp only [found, pure, Except.pure, owner, ordinary, Option.filter_none, evidenceNone]
    rcases shape with ⟨name, binder, form, generalized⟩ | ⟨ids, form⟩ | ⟨literal, resolution, form⟩
    · simp only [form, generalized, Bool.false_eq_true, ↓reduceIte]
    · simp only [form]
    · simp only [form]

/-- The original parent output is accepted under the initializer's SAME fixed
policy and body callback. Only the actual four finite compiler branches are
reduced; no policy equality or fresh contextual selector is required. -/
theorem CompilerCalls.parent_at_initializer_root {packet : Packet} {given : Graph packet}
    (calls : CompilerCalls packet given) (rows : ParentRows packet given)
    (checked : ordinaryParentAction packet calls = .ok calls.parent)
    (compilation : Compilation packet.compiled.indexed packet.named
      (effectiveDiagnostics packet.compiled packet.diagnostics) packet.namedCode) :
    let root := calls.initializer_root compilation
    SourceCoreFunctions.lowerExpressionWithPolicy root.root.selected.policy root.root.selected.lowerBody 498
      (context packet.compiled.indexed packet.named) (source packet.named)
      ((given.binder.id, calls.payload) :: initialScope packet) (expressionId packet 5)
      ((effectiveDiagnostics packet.compiled packet.diagnostics).reasonAt packet.named.signature.key) = .ok calls.parent := by
  let root := calls.initializer_root compilation
  let scope := (given.binder.id, calls.payload) :: initialScope packet
  let reasonAt := (effectiveDiagnostics packet.compiled packet.diagnostics).reasonAt packet.named.signature.key
  have emptyOwned (node : ExpressionNode) (requirements : node.requirements = []) (coercions : node.coercions = []) :
      SourceCompilationPlan.ordinaryOwnedRequirements? node = some [] := by
    unfold SourceCompilationPlan.ordinaryOwnedRequirements?
    rw [requirements, coercions]
    rfl
  have leftPolicy := ordinary_pointwise root.root (childScope := scope) rows.leftFound
    (.inr (.inr ⟨_, _, rows.leftForm⟩)) rows.leftOwned rows.leftCoercions
    (.inr ⟨_, _, rows.leftForm⟩) rows.leftOrdinary
  have rightPolicy := ordinary_pointwise root.root (childScope := scope) rows.rightFound
    (.inr (.inr ⟨_, _, rows.rightForm⟩)) rows.rightOwned rows.rightCoercions
    (.inr ⟨_, _, rows.rightForm⟩) rows.rightOrdinary
  have calleePolicy := ordinary_pointwise root.root (childScope := scope) given.calleeFound
    (.inl ⟨_, _, given.calleeForm, rows.generalized⟩)
    (emptyOwned given.callee rows.calleeRequirements rows.calleeCoercions) rows.calleeCoercions
    (.inl rows.calleeRequirements) rows.calleeOrdinary
  have argumentPolicy := ordinary_pointwise root.root (childScope := scope) given.argumentFound
    (.inr (.inl ⟨_, given.argumentForm⟩))
    (emptyOwned given.argument rows.argumentRequirements rows.argumentCoercions) rows.argumentCoercions
    (.inl rows.argumentRequirements) rows.argumentOrdinary
  have parentPolicy := CallableIndexedOwnedContextualCompilerPolicyProfiles.indirect_policy root.root
    (scope := scope) (reasonAt := reasonAt) given.parentFound given.parentForm given.parentRequirements given.parentCoercions rfl calls.parentOrdinary
  have bypass (id : ExpressionId) : SpecialNone (ordinaryPolicy packet)
      (context packet.compiled.indexed packet.named) (source packet.named) scope id reasonAt := by intro child budget; rfl
  have leftSame := integer_branch_same (firstBody := root.root.selected.lowerBody)
    (second := ordinaryPolicy packet) (secondBody := ordinaryBody packet calls)
    495 rfl rows.leftFound rows.leftForm leftPolicy.special (bypass _)
  have rightSame := integer_branch_same (firstBody := root.root.selected.lowerBody)
    (second := ordinaryPolicy packet) (secondBody := ordinaryBody packet calls)
    495 rfl rows.rightFound rows.rightForm rightPolicy.special (bypass _)
  have calleeSame := reference_branch_same (firstBody := root.root.selected.lowerBody)
    (second := ordinaryPolicy packet) (secondBody := ordinaryBody packet calls)
    496 rfl given.calleeFound given.calleeForm calleePolicy.special (bypass _)
    (calleePolicy.read.trans rows.calleeRead) rows.calleeRead root.lowerRead
  have argumentSame := tuple_branch_same (firstBody := root.root.selected.lowerBody)
    (second := ordinaryPolicy packet) (secondBody := ordinaryBody packet calls)
    496 rfl given.argumentFound given.argumentForm argumentPolicy.special (bypass _)
    (argumentPolicy.read.trans rows.argumentRead) rows.argumentRead leftSame rightSame
  have parentSame := indirect_branch_same (firstBody := root.root.selected.lowerBody)
    (second := ordinaryPolicy packet) (secondBody := ordinaryBody packet calls)
    497 rfl given.parentFound given.parentForm parentPolicy.special (bypass _)
    (parentPolicy.read.trans rows.parentRead) rows.parentRead calleePolicy.read
    root.root.projectType root.root.selected.callables calleeSame argumentSame
  exact parentSame.trans checked

def runtimeContext (packet : Packet) : SourceSemantics.Context :=
  SourceSemantics.declarationContext packet.compiled.sourceProgram.signatures
    (source packet.named).owner [] [] packet.named.specialized.function.solvedRequirements

/-- The finite receipt checks the unchanged Source graph and real numeric
ledger. Its declaration context fields are literal constructor projections. -/
structure RuntimeReceipt (packet : Packet) : Prop where
  graph : CallableIndexedOwnedFiniteSourceRuntimeReceipts.checkGraph (source packet.named) = true
  rows : packet.named.specialized.function.solvedRequirements = numericRows

def runtimeReceipt (packet : Packet) : Except String (PLift (RuntimeReceipt packet)) := do
  let rows ← numericLedger packet
  if accepted : CallableIndexedOwnedFiniteSourceRuntimeReceipts.checkGraph (source packet.named) = true then
    pure ⟨⟨accepted, rows.down⟩⟩
  else throw "actual unchanged occurrence graph failed its finite invariant check"

theorem RuntimeReceipt.source_runtime {packet : Packet} (receipt : RuntimeReceipt packet) :
    Dynamic.SourceRuntimeValid (Program.ofChecked packet.compiled.sourceProgram)
      (runtimeContext packet) (source packet.named) := by
  apply CallableIndexedOwnedFiniteSourceRuntimeReceipts.source_runtime
    (fields := ⟨rfl, rfl, rfl, rfl, rfl⟩) receipt.graph
  apply numeric_runtime_ledger
  exact receipt.rows

/-- This bundle is returned only after every actual compiler, metadata and
graph check succeeds. It retains the original output as the shared-policy target. -/
structure AcceptedFixture where
  packet : Packet
  graph : Graph packet
  calls : CompilerCalls packet graph
  tail : NamedTail packet calls
  parentRows : ParentRows packet graph
  parentAccepted : ordinaryParentAction packet calls = .ok calls.parent
  runtime : RuntimeReceipt packet

def acceptedFixture : Except String AcceptedFixture := do
  let packet ← prepare
  let given ← graph packet
  let calls ← compilerCalls packet given
  let tail ← namedTail packet calls
  let rows ← parentRows packet given
  let accepted ← ordinaryParent packet calls
  let runtime ← runtimeReceipt packet
  pure ⟨packet, given, calls, tail, rows, accepted.down, runtime.down⟩

/-- The sealed named producer supplies the Compilation. Exactly one
initializer selector then retains the original parent output at its fixed policy. -/
theorem AcceptedFixture.same_root_parent (fixture : AcceptedFixture) :
    ∃ compilation : Compilation fixture.packet.compiled.indexed fixture.packet.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode,
    let root := fixture.calls.initializer_root compilation
    SourceCoreFunctions.lowerExpressionWithPolicy root.root.selected.policy root.root.selected.lowerBody 498
      (context fixture.packet.compiled.indexed fixture.packet.named) (source fixture.packet.named)
      ((fixture.graph.binder.id, fixture.calls.payload) :: initialScope fixture.packet) (expressionId fixture.packet 5)
      ((effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key) =
      .ok fixture.calls.parent := by
  obtain ⟨compilation⟩ := fixture.packet.named_compilation
  exact ⟨compilation, fixture.calls.parent_at_initializer_root fixture.parentRows fixture.parentAccepted compilation⟩

def run : IO Unit := do
  match acceptedFixture with
  | .error error => throw (IO.userError error)
  | .ok fixture =>
    let packet := fixture.packet
    let source := CallableIndexedNamedGeneration.source packet.named
    let lambdas := source.nodes.filter fun
      | .expression node => match node.form with | .lambda _ _ _ => true | _ => false
      | _ => false
    let indirect := source.nodes.filter fun
      | .expression node => match node.form with | .call _ _ (.indirect _) => true | _ => false
      | _ => false
    SourceCompilerFeatureSupport.require (lambdas.length == 1 && indirect.length == 1)
      "the untouched accepted Source must retain one lambda and its indirect parent"
    IO.println "accepted fixture: original compiler equations, same initializer-root parent output, numeric ledger and finite runtime graph retained; external indirect parent lies outside the literal body domain"

end Tests.SourceCoreChosenOrdinaryAcceptedFixture
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedBodyMetadata
/-! Finite static receipts from the unchanged accepted lambda fixture.
These checks retain actual statement projection and occurrence metadata.
Source typing and body execution remain separate judgments. -/
set_option autoImplicit false
namespace Tests.SourceCoreChosenOrdinaryAcceptedBodyMetadata
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SourceCoreChosenOrdinaryAcceptedFixture
open CallableIndexedNamedGeneration

/-- Reject match forms anywhere in the actual retained node table. -/
def checkNoMatches (view : TypedSource) : Bool :=
  view.nodes.all fun
    | .expression _ => true
    | .statement node => match node.form with
      | .matchWith _ => false
      | _ => true

/-- Read every expression's original retained output-coercion list. -/
def checkEmptyCoercions (view : TypedSource) : Bool :=
  view.nodes.all fun
    | .statement _ => true
    | .expression node => node.coercions.isEmpty

theorem no_matches_of_checked {view : TypedSource}
    (accepted : checkNoMatches view = true) :
    ∀ statement node, view.lookupStatement? statement = some node →
      ∀ resolution, node.form ≠ .matchWith resolution := by
  intro statement node found resolution same
  have member := (SourceSemantics.lookupStatement?_sound found).1
  have checked := List.all_eq_true.mp accepted (.statement node) member
  change (match node.form with | .matchWith _ => false | _ => true) = true at checked
  rw [same] at checked
  contradiction

theorem empty_coercions_of_checked {view : TypedSource}
    (accepted : checkEmptyCoercions view = true) :
    ∀ expression node, view.lookupExpression? expression = some node → node.coercions = [] := by
  intro expression node found
  have member := (SourceSemantics.lookupExpression?_sound found).1
  have checked := List.all_eq_true.mp accepted (.expression node) member
  change node.coercions.isEmpty = true at checked
  cases rows : node.coercions with
  | nil => rfl
  | cons _ _ => simp only [rows, List.isEmpty_cons, Bool.false_eq_true] at checked

/-- Static facts obtained by checking the actual node table and checked
projection; no compiler output, Source node or requirement is replaced. -/
structure Receipt (packet : Packet) (given : Graph packet) : Prop where
  noMatches : checkNoMatches (source packet.named) = true
  emptyCoercions : checkEmptyCoercions (source packet.named) = true
  inputs : packet.named.inputs = []
  projected : SourceCoreCompatibleDataExpressions.projectType packet.compiled.compatible.checked
    (.occurrence (statementId packet 2).occurrence) given.returned.type = .ok .word

/-- Each successful finite check retains its original equation. -/
def receipt (packet : Packet) (given : Graph packet) : Except String (PLift (Receipt packet given)) := do
  if noMatches : checkNoMatches (source packet.named) = true then
    if emptyCoercions : checkEmptyCoercions (source packet.named) = true then
      if noInputs : packet.named.inputs.isEmpty = true then
        have inputs : packet.named.inputs = [] := by
          cases rows : packet.named.inputs with
          | nil => rfl
          | cons _ _ => simp only [rows, List.isEmpty_cons, Bool.false_eq_true] at noInputs
        match projected : SourceCoreCompatibleDataExpressions.projectType packet.compiled.compatible.checked
            (.occurrence (statementId packet 2).occurrence) given.returned.type with
        | .ok .word => pure ⟨⟨noMatches, emptyCoercions, inputs, projected⟩⟩
        | _ => throw "actual inner return projection differs from Word"
      else throw "actual named parameter list is nonempty"
    else throw "actual retained Source contains an output coercion"
  else throw "actual retained Source contains a match form"

theorem Receipt.no_matches {packet : Packet} {given : Graph packet}
    (checked : Receipt packet given) :
    ∀ statement node, (source packet.named).lookupStatement? statement = some node →
      ∀ resolution, node.form ≠ .matchWith resolution :=
  no_matches_of_checked checked.noMatches

theorem Receipt.empty_coercions {packet : Packet} {given : Graph packet}
    (checked : Receipt packet given) :
    ∀ expression node, (source packet.named).lookupExpression? expression = some node → node.coercions = [] :=
  empty_coercions_of_checked checked.emptyCoercions

/-- Original lookup and checked projection yield the real compatible read. -/
theorem Receipt.return_read {packet : Packet} {given : Graph packet}
    (checked : Receipt packet given) :
    SourceCoreCompatibleDataExpressions.readStatement packet.compiled.compatible.checked
      (source packet.named) (statementId packet 2) = .ok (given.returned, .word) := by
  unfold SourceCoreCompatibleDataExpressions.readStatement
  have owner : (statementId packet 2).occurrence.owner = (source packet.named).owner := rfl
  simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte]
  rw [given.returnedFound]
  simp only [checked.projected, bind, Except.bind, pure, Except.pure]

/-- Empty compiler scope has no visible native binder needing a Source
local declaration; this retains the caller's actual declaration context. -/
theorem Receipt.initial_declarations {packet : Packet} {given : Graph packet}
    (checked : Receipt packet given) :
    CompatibleExpressionReads.ScopeDeclarations (source packet.named) (initialScope packet)
      (runtimeContext packet) := by
  intro binder declared index type found _root
  have scope : initialScope packet = [] := by
    simp only [initialScope, checked.inputs, List.reverse_nil, List.map_nil]
  rw [scope] at found
  cases found

/-- A real finite consumer of the retained compiler/metadata fixture. -/
def run : IO Unit := do
  match acceptedFixture with
  | .error error => throw (IO.userError error)
  | .ok fixture =>
    match receipt fixture.packet fixture.graph with
    | .error error => throw (IO.userError error)
    | .ok _ => IO.println "accepted literal body metadata: original return projection, no match forms and empty output coercions checked"

end Tests.SourceCoreChosenOrdinaryAcceptedBodyMetadata
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedHeader
/-! An actual named Header for the accepted fixture. Original worklist selection
and executable-plan growth authenticate the complete specialization. The finite
metadata check and independent graph/ledger receipt supply its Source context;
no program body meaning or native-code provenance is an input. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreChosenOrdinaryAcceptedHeader
open Solcore Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering Core
open CallableIndexedNamedGeneration
open Tests.SourceCoreChosenOrdinaryAcceptedFixture

/-- The selected row belongs to the original successful worklist action. -/
structure OriginalSelection (packet : Packet) where
  row : SourceSpecialization.SpecializedFunction
  accepted : SourceCompilationPlan.exactSpecialization packet.plan packet.named.signature.key = .ok row

def originalSelection (packet : Packet) : Except String (OriginalSelection packet) :=
  match accepted : SourceCompilationPlan.exactSpecialization packet.plan packet.named.signature.key with
  | .error error => .error s!"original worklist selection: {reprStr error}"
  | .ok row => .ok ⟨row, accepted⟩

/-- The prepared plan preserves the entire original row, not just its key. -/
theorem OriginalSelection.same (packet : Packet) (selected : OriginalSelection packet) :
    selected.row = packet.named.specialized := by
  obtain ⟨programEq, planEq, _⟩ := SourceCoreUnifiedPreparationCertificates.prepare_fields packet.compiledAccepted
  have prepared := SourceCoreUnifiedPreparationCertificates.compiled_planPrepared packet.compiled
  rw [programEq, planEq] at prepared
  obtain ⟨growth, _⟩ := CallableCoercionPreparation.of_accepted prepared
  have retained := growth.selected _ _ selected.accepted
  exact Except.ok.inj (retained.symm.trans packet.named_record)

theorem OriginalSelection.origin (packet : Packet) (selected : OriginalSelection packet) :
    RecursiveNamedPublicSpecializationMeaning.Origin packet.compiled.sourceProgram packet.named.specialized := by
  have member := (CallableNamedMetadata.specialization_of_exact selected.accepted).1
  have origin := RecursiveNamedPublicSpecializationMeaning.worklist_origins packet.worklist selected.row member
  have programEq := (SourceCoreUnifiedPreparationCertificates.prepare_fields packet.compiledAccepted).1
  simpa only [programEq, selected.same packet] using origin

/-- Every field is checked on the unchanged selected named row. -/
structure Metadata (packet : Packet) : Prop where
  owner : (source packet.named).owner = packet.named.specialized.declaration
  inputs : (source packet.named).inputs = []
  substitution : packet.named.specialized.parameterSubstitution = []
  assumptions : packet.named.specialized.assumptions = []
  ordinary : packet.named.specialized.function.returnComptime = false
  parameter : packet.named.signature.parameterType = .unit
  target : SourceCompilationPlan.exactInstantiationKey packet.compiled.indexed.base.plan
    (CallableNamedMetadata.instantiation packet.named.specialized) = .ok packet.named.signature.key

def metadata (packet : Packet) : Except String (PLift (Metadata packet)) := do
  if owner : (source packet.named).owner = packet.named.specialized.declaration then
    if inputs : (source packet.named).inputs = [] then
      if substitution : packet.named.specialized.parameterSubstitution = [] then
        if assumptions : packet.named.specialized.assumptions = [] then
          if ordinary : packet.named.specialized.function.returnComptime = false then
            if parameter : packet.named.signature.parameterType = .unit then
              match target : SourceCompilationPlan.exactInstantiationKey packet.compiled.indexed.base.plan
                  (CallableNamedMetadata.instantiation packet.named.specialized) with
              | .error error => throw s!"actual instantiation target: {reprStr error}"
              | .ok key =>
                if same : key = packet.named.signature.key then
                  pure ⟨⟨owner, inputs, substitution, assumptions, ordinary, parameter, by simpa only [same] using target⟩⟩
                else throw "actual instantiation target has another named key"
            else throw "actual named parameter type is not unit"
          else throw "actual named return is staged"
        else throw "actual named assumptions are nonempty"
      else throw "actual named substitution is nonempty"
    else throw "actual named inputs are nonempty"
  else throw "actual Source owner disagrees with the specialization"

theorem Metadata.named_inputs {packet : Packet} (checked : Metadata packet) : packet.named.inputs = [] := by
  have same := (RecursiveNamedPreparedParameterProjections.cached_inputs packet.compiled packet.namedSelected).1
  change packet.named.inputs.map Prod.fst = (source packet.named).inputs at same
  rw [checked.inputs] at same
  exact List.map_eq_nil_iff.mp same

/-- The named declaration context is exactly the already validated context. -/
theorem Metadata.view_context {packet : Packet} (checked : Metadata packet) (statements : List StatementId) :
    (RecursiveNamedPreparedSourceFrames.view packet.compiled.sourceProgram packet.named statements).context =
      runtimeContext packet := by
  simp only [RecursiveNamedPreparedSourceFrames.view, RecursiveNamedSpecializationBodyFacts.bodyInstance,
    runtimeContext, checked.assumptions, checked.owner]

abbrev ActualHeader (fixture : AcceptedFixture) :=
  CallableIndexedOwnedFunctionValues.Header fixture.packet.compiled (Program.ofChecked fixture.packet.compiled.sourceProgram)

/-- This is the original named-body callback, with its actual retained fields. -/
def policy (fixture : AcceptedFixture) : SourceCoreLoops.Policy :=
  let packet := fixture.packet
  let actual := (representation packet.compiled.indexed).atContext packet.named.signature.key []
  let diagnostics := effectiveDiagnostics packet.compiled packet.diagnostics
  let expression := SourceCoreGeneralFunctions.lowerContextualExpression packet.compiled.indexed.base.sourceProgram actual
    packet.compiled.indexed.base.sourceProgram.signatures packet.compiled.indexed.base.locals fixture.calls.parents
    fixture.calls.own.assignments diagnostics (context packet.compiled.indexed packet.named)
    packet.compiled.indexed.base.callableContext none none
  { actual.loopsWithSourceCells actual.expressions.sourceCells packet.named.specialized.function.solvedRequirements
      fixture.calls.own.assignments diagnostics packet.named.signature.key expression with
    sourceCells := actual.expressions.sourceCells
    lowerBinder := SourceCoreGeneralFunctions.contextualBinder actual packet.compiled.indexed.base.locals packet.named.signature.key [] }

/-- The returned Header retains the original accepted body, prefix and hook. -/
structure HeaderAt (fixture : AcceptedFixture) (header : ActualHeader fixture) : Prop where
  named : header.named = fixture.packet.named
  source : header.function.source = source fixture.packet.named
  context : header.context = runtimeContext fixture.packet
  functionContext : header.function.context = runtimeContext fixture.packet
  parameters : header.function.parameters = []
  bindings : header.bindings = fixture.packet.named.inputs
  body : header.body = fixture.calls.body
  parameterCode : header.parameterCode = fixture.tail.parameters
  code : header.code = fixture.tail.output
  slot : header.slot = 0
  ledger : header.solved = fixture.packet.named.specialized.function.solvedRequirements
  fuel : header.fuel = 500
  readFuel : header.readFuel = 500
  statements : header.function.body = [statementId fixture.packet 0, statementId fixture.packet 4]
  policy : header.policy = policy fixture
  accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
    (header.bindings.reverse.map fun binding => (binding.1.id, binding.2)) header.function.body header.output
    header.reasonAt header.fellThrough header.escaped = .ok header.body

/-- The source frame uses original specialization and preparation receipts. -/
theorem source_frame (fixture : AcceptedFixture) (selected : OriginalSelection fixture.packet)
    (checked : Metadata fixture.packet)
    (compilation : Compilation fixture.packet.compiled.indexed fixture.packet.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode) :
    NamedCalls.SourceFrame (Program.ofChecked fixture.packet.compiled.sourceProgram)
      (CallableNamedMetadata.instantiation fixture.packet.named.specialized)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance fixture.packet.compiled.sourceProgram fixture.packet.named.specialized)
      (RecursiveNamedPreparedSourceFrames.view fixture.packet.compiled.sourceProgram fixture.packet.named compilation.statements) := by
  obtain ⟨request, signature, generic, signatureMember, genericMember, _, specialized⟩ := selected.origin fixture.packet
  have programEq := (SourceCoreUnifiedPreparationCertificates.prepare_fields fixture.packet.compiledAccepted).1
  have catalog := SignatureCatalogWellFormed.ofCheckProgram fixture.packet.checked
  rw [← programEq] at catalog
  have unique := (catalog.function_parameters signature signatureMember).1
  have range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures fixture.packet.compiled.sourceProgram.signatures)
      fixture.packet.named.specialized.parameterSubstitution := by
    rw [checked.substitution]
    intro entry replacement member
    cases member
  obtain ⟨row, _, prepared⟩ := RecursiveNamedPreparedParameterProjections.cached_preparation
    fixture.packet.compiled fixture.packet.namedSelected
  exact (RecursiveNamedSpecializationValidity.of_compilation signatureMember genericMember specialized unique range
    checked.assumptions prepared compilation).2

/-- Actual accepted compiler receipts and independent finite Source validity
construct the Header. The sealed Compilation is eliminated only into Prop. -/
theorem header_exists (fixture : AcceptedFixture) (selected : OriginalSelection fixture.packet)
    (checked : Metadata fixture.packet) : ∃ header : ActualHeader fixture, HeaderAt fixture header := by
  obtain ⟨compilation⟩ := fixture.packet.named_compilation
  let function := RecursiveNamedPreparedSourceFrames.view fixture.packet.compiled.sourceProgram fixture.packet.named compilation.statements
  have frame := source_frame fixture selected checked compilation
  obtain ⟨row, _, prepared⟩ := RecursiveNamedPreparedParameterProjections.cached_preparation
    fixture.packet.compiled fixture.packet.namedSelected
  have agreement := RecursiveNamedPreparedSourceFrames.agreement prepared compilation
  have namedInputs := checked.named_inputs
  have parameters : function.parameters = [] := checked.inputs
  have sameContext : function.context = runtimeContext fixture.packet := checked.view_context compilation.statements
  have extended : MonoBindersExtend function.source.owner function.context function.parameters [] (runtimeContext fixture.packet) := by
    rw [parameters, sameContext]
    exact .nil _
  have valid : CompatibleRuntimeContextValidity.Valid fixture.packet.named.specialized.function.solvedRequirements
      (runtimeContext fixture.packet) function.evidence := by
    refine ⟨rfl, ?_, ?_⟩
    · exact fixture.runtime.source_runtime.requirements
    · have covers := RecursiveNamedPreparedSourceFrames.empty_covers (program := fixture.packet.compiled.sourceProgram) checked.assumptions
      rw [← sameContext]
      exact covers
  have unique : NodeOccurrencesUnique function.source := fixture.runtime.source_runtime.graph.nodeOccurrencesUnique
  have parameterType : fixture.packet.named.signature.parameterType =
      SourceCoreCompatibleCatalog.packTypes (fixture.packet.named.inputs.map Prod.snd) := by
    rw [namedInputs, List.map_nil]
    exact checked.parameter
  let header := RecursiveNamedCatalog.Header.of_dictionary_body
    (values := .initial fixture.packet.compiled.compatible.checked)
    (function := function) (instantiation := CallableNamedMetadata.instantiation fixture.packet.named.specialized)
    (sourceBody := RecursiveNamedSpecializationBodyFacts.bodyInstance fixture.packet.compiled.sourceProgram fixture.packet.named.specialized)
    (frame := frame) (named := fixture.packet.named) (agreement := agreement)
    (ordinaryReturn := checked.ordinary) (ordinaryParameters := by intro binder member; rw [parameters] at member; cases member)
    (target := checked.target) (context := runtimeContext fixture.packet) (types := []) (bindings := fixture.packet.named.inputs)
    (parameters := agreement.parameters) (inputs := agreement.parameters) (extended := extended)
    (solved := fixture.packet.named.specialized.function.solvedRequirements)
    (reasonAt := (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key)
    (readFuel := fixture.packet.compiled.indexed.fuel) (output := fixture.packet.named.signature.resultType)
    (policy := policy fixture)
    (fuel := fixture.packet.compiled.indexed.fuel) (fellThrough := compilation.own.fellThroughReason)
    (escaped := compilation.own.table.escapedReason) (body := compilation.body) (parameterCode := compilation.parameterCode)
    (code := compilation.output) (layouts := fixture.packet.compiled.indexed.layouts)
    (owner := fixture.packet.named.signature.key) (active := []) (globals := fixture.packet.compiled.indexed.base.globals.length)
    (onError := fun error => .sourceAllocation (reprStr error)) (acceptedPrefix := compilation.parametersCompiled)
    (hook := compilation.hook) (definitions_eq := rfl) (registered := CallableIndexedAmbient.frame_registered fixture.packet.compiled.indexed)
    (valid := valid) (unique := unique) (parameterType := parameterType) (resultType := rfl)
    (representation := representation fixture.packet.compiled.indexed) (compiledFuel := fixture.packet.compiled.indexed.fuel)
    (compiled := fixture.packet.compiled.indexed.secondPass) (slot := 0) (selected := fixture.packet.namedSelected)
    (cached := fixture.packet.cached.trans (congrArg some compilation.emitted))
  obtain ⟨parentsEq, ownEq, statementsEq, bodyEq⟩ := fixture.calls.compilation_alignment compilation
  obtain ⟨parametersEq, outputEq⟩ := fixture.tail.compilation_alignment compilation
  refine ⟨header, ⟨rfl, rfl, rfl, sameContext, parameters, rfl, bodyEq, parametersEq, outputEq, rfl, rfl,
    fixture.calls.fuel, fixture.calls.fuel, statementsEq, rfl, ?_⟩⟩
  simpa only [header, function, RecursiveNamedPreparedSourceFrames.view, ownEq, statementsEq, bodyEq,
    CallableIndexedNamedGeneration.source, bodyAction, SourceCoreGeneralFunctions.bodyLowererWithRepresentation,
    policy] using fixture.calls.bodyCompiled

theorem source_runtime_at_header (fixture : AcceptedFixture) {header : ActualHeader fixture}
    (atHeader : HeaderAt fixture header) :
    Dynamic.SourceRuntimeValid (Program.ofChecked fixture.packet.compiled.sourceProgram) header.context header.function.source := by
  rw [atHeader.context, atHeader.source]
  exact fixture.runtime.source_runtime

/-- The executable checks retain original compiler provenance and finite
metadata. The actual Header is constructed by the theorem below. -/
structure HeaderFixture where
  fixture : AcceptedFixture
  selected : OriginalSelection fixture.packet
  checked : Metadata fixture.packet

def acceptedHeaderFixture : Except String HeaderFixture := do
  let fixture ← acceptedFixture
  let selected ← originalSelection fixture.packet
  let checked ← metadata fixture.packet
  pure ⟨fixture, selected, checked.down⟩

theorem HeaderFixture.header (given : HeaderFixture) :
    ∃ header : ActualHeader given.fixture, HeaderAt given.fixture header :=
  header_exists given.fixture given.selected given.checked

theorem HeaderFixture.runtime (given : HeaderFixture) :
    ∃ header : ActualHeader given.fixture, HeaderAt given.fixture header ∧
      Dynamic.SourceRuntimeValid (Program.ofChecked given.fixture.packet.compiled.sourceProgram)
        header.context header.function.source := by
  obtain ⟨header, atHeader⟩ := given.header
  exact ⟨header, atHeader, source_runtime_at_header given.fixture atHeader⟩

theorem Metadata.initial_scope {packet : Packet} (checked : Metadata packet) : initialScope packet = [] := by
  simp only [initialScope, checked.named_inputs, List.reverse_nil, List.map_nil]

def run : IO Unit := do
  match acceptedHeaderFixture with
  | .error error => throw (IO.userError error)
  | .ok _ =>
    IO.println "accepted Header fixture: original worklist row and compiler metadata checks passed; Header and its exact Source runtime context are constructed by the kernel proofs"

end Tests.SourceCoreChosenOrdinaryAcceptedHeader
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedBodyStatePorts
/-! The real empty parameter allocation retains its Source heap and lexical
environment. The same reached receipt supplies captures, native observations,
the principal packet, marked readiness and deep Source admission. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreChosenOrdinaryAcceptedBodyStatePorts
open Solcore Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering Core
open GeneralHeap ReadOnly CompatiblePayload CallableIndexedHistory
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open Tests.SourceCoreChosenOrdinaryAcceptedFixture
open Tests.SourceCoreChosenOrdinaryAcceptedHeader

variable (fixture : AcceptedFixture) {header : ActualHeader fixture}
  (atHeader : HeaderAt fixture header)
  {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.packet.compiled
    (Program.ofChecked fixture.packet.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key fixture.packet.compiled
    (Program.ofChecked fixture.packet.compiled.sourceProgram))}
  (functions : FunctionModel fixture.packet.compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {initial : ProtectedStateTransition.Index}
  {argumentsPool : State headers keys initial} {arguments : List Dynamic.Value}
  (receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt
    (registry := registry) functions owner argumentsPool header arguments)

include atHeader in
/-- The genuine Header parameter equation fixes the exact empty binding list. -/
theorem bindings_empty : header.bindings = [] := by
  have same : header.bindings.map Prod.fst = [] := header.parameters.symm.trans atHeader.parameters
  exact List.map_eq_nil_iff.mp same

private theorem empty_allocation {before heap : Dynamic.Heap} {values : List Dynamic.Value}
    {environment : Dynamic.Environment}
    (allocated : Dynamic.BindersAllocate [] before [] values environment heap) :
    values = [] ∧ environment = [] ∧ heap = before := by
  cases allocated
  exact ⟨rfl, rfl, rfl⟩

include atHeader in
/-- Empty parameters admit only the original nil allocation constructor. -/
theorem empty_entry : arguments = [] ∧ receipt.body.environment = [] ∧ receipt.body.heap = initial.heap := by
  have allocation := receipt.body.allocation
  rw [atHeader.parameters] at allocation
  exact empty_allocation allocation

include atHeader in
/-- The Header and fixture scopes denote the same literal empty Source scope. -/
theorem scope_at_entry :
    header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)) = initialScope fixture.packet := by
  exact congrArg (fun bindings => bindings.reverse.map (fun binding => (binding.1.id, binding.2))) atHeader.bindings

include atHeader in
theorem scope_empty : initialScope fixture.packet = [] := by
  rw [← scope_at_entry fixture atHeader, bindings_empty fixture atHeader]
  rfl

include atHeader in
/-- The actual parameter temporaries vanish only because their binding list is empty. -/
theorem actual_environment_typed : RuntimeEnvironmentHasTypes receipt.body.world receipt.body.actualBody
    receipt.actualContext fixture.packet.compiled.indexed.layouts.definitions := by
  simpa only [bindings_empty fixture atHeader, CallableIndexedParameterTyped.prefixContext, List.foldl_nil, SourceCoreCompatibleValues.Context.initial, CallableIndexedAmbient.ambientDefinitions]
    using receipt.body.actualTyped

/-- Store typing is an original field of the same receiving-model heap relation. -/
theorem runtime_store_typed : RuntimeStoreHasTypes receipt.body.world receipt.body.store
    fixture.packet.compiled.indexed.layouts.definitions := receipt.body.heaps.runtime_hasTypes

include atHeader in
theorem source_heap_typed : Dynamic.HeapWellTyped (runtimeContext fixture.packet) receipt.body.heap := by
  rw [(empty_entry fixture atHeader functions owner receipt).2.2, ← atHeader.functionContext]
  exact receipt.heapTyped

include atHeader in
theorem source_locals : Dynamic.EnvironmentAgrees receipt.body.heap (runtimeContext fixture.packet).locals [] := by
  simpa only [atHeader.context, (empty_entry fixture atHeader functions owner receipt).2.1] using receipt.body.locals

/-- Catalog, carried Source metadata, bundle and frame come from the same entry. -/
def formation_entry (prefixZero : owner.key.capturePrefix = 0) :
    CallableIndexedLambdaNestedFormationEntries.Entry
      (values := .initial fixture.packet.compiled.compatible.checked)
      (indexed := fixture.packet.compiled.indexed)
      (program := Program.ofChecked fixture.packet.compiled.sourceProgram) header headers owner.key.locations 0 1
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      receipt.body.mapping receipt.body.world receipt.body.heap receipt.body.store receipt.body.canonical where
  catalog := {
    authority := {
      frameLocation := receipt.body.catalog.authority.frameLocation
      unmapped := receipt.body.catalog.authority.unmapped
      typed := receipt.body.catalog.authority.typed
      current := receipt.body.catalog.authority.current
      ghost := receipt.body.catalog.authority.ghost
      frame := receipt.body.catalog.authority.frame
      records := receipt.body.catalog.authority.records
      snapshots := receipt.body.catalog.authority.snapshots
      distinct := receipt.body.catalog.authority.distinct
      captures := by
        intro target member
        obtain ⟨capture⟩ := receipt.body.catalog.authority.captures target member
        exact ⟨{ capture with
          coherent := by
            intro other retained
            simpa only [prefixZero] using capture.coherent other retained }⟩ }
    globals := by
      intro target member
      simpa only [prefixZero, Nat.zero_add] using receipt.body.catalog.globals target member }
  history := by
    simpa only [receipt.body.catalog_current, receipt.body.catalog_ghost, SourceCoreCompatibleValues.Context.initial] using receipt.allowed.2
  bundle := CallableIndexedLambdaNestedFormationEntries.bundle_of_environment receipt.body.environments
    (by rw [header.parameterType]; rfl)
  reference := by
    simpa only [List.length_map, List.length_reverse, receipt.body.catalog_frame] using receipt.body.reference

/-- Construct the finite creator capture without replaying the parameter prefix. -/
def captures_at_entry
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (prepared := fixture.packet.compiled.indexed.ancestry)
      (values := .initial fixture.packet.compiled.compatible.checked)
      (program := Program.ofChecked fixture.packet.compiled.sourceProgram)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed) headers)
    (prefixZero : owner.key.capturePrefix = 0)
    (globals : header.globals = fixture.packet.compiled.indexed.base.globals.length) :
    CallableIndexedLambdaValues.Captures fixture.packet.compiled.indexed receipt.body.mapping receipt.body.world
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      receipt.body.environment receipt.body.actualBody :=
  RecursiveNamedLambdaFormationHeads.captures_for complete globals
    (formation_entry fixture functions owner receipt prefixZero)
    receipt.body.environments receipt.body.lookups receipt.body.actualTyped

theorem captures_prefix
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (prepared := fixture.packet.compiled.indexed.ancestry)
      (values := .initial fixture.packet.compiled.compatible.checked)
      (program := Program.ofChecked fixture.packet.compiled.sourceProgram)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed) headers)
    (prefixZero : owner.key.capturePrefix = 0)
    (globals : header.globals = fixture.packet.compiled.indexed.base.globals.length) :
    (captures_at_entry fixture functions owner receipt complete prefixZero globals).administrative =
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial fixture.packet.compiled.compatible.checked) header := rfl

theorem captures_embedding
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (prepared := fixture.packet.compiled.indexed.ancestry)
      (values := .initial fixture.packet.compiled.compatible.checked)
      (program := Program.ofChecked fixture.packet.compiled.sourceProgram)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed) headers)
    (prefixZero : owner.key.capturePrefix = 0)
    (globals : header.globals = fixture.packet.compiled.indexed.base.globals.length) :
    (captures_at_entry fixture functions owner receipt complete prefixZero globals).embedding = receipt.body.embedding := rfl

/-- Actual cached Header slots bound the capture; no global completeness inverse is used. -/
theorem captured_globals
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (prepared := fixture.packet.compiled.indexed.ancestry)
      (values := .initial fixture.packet.compiled.compatible.checked)
      (program := Program.ofChecked fixture.packet.compiled.sourceProgram)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed) headers)
    (prefixZero : owner.key.capturePrefix = 0)
    (globals : header.globals = fixture.packet.compiled.indexed.base.globals.length) :
    CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := fixture.packet.compiled.indexed)
      (values := .initial fixture.packet.compiled.compatible.checked)
      (program := Program.ofChecked fixture.packet.compiled.sourceProgram)
      headers owner.key.locations 1
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      (captures_at_entry fixture functions owner receipt complete prefixZero globals).canonical owner.key.frameLocation := by
  have observed := RecursiveNamedLambdaFormationHeads.capture_globals_for complete globals
    (RecursiveNamedLambdaFormationHeads.cached_capture_slots fixture.packet.compiled headers)
    (formation_entry fixture functions owner receipt prefixZero)
    receipt.body.environments receipt.body.lookups receipt.body.actualTyped
  simpa only [captures_at_entry, RecursiveNamedLambdaFormationHeads.captures_for,
    formation_entry, receipt.body.catalog_frame, receipt.physical] using observed

include atHeader in
/-- Deep Source typing and every installed row concern the unchanged reached pool. -/
theorem admission_at_entry (prefixZero : owner.key.capturePrefix = 0)
    (globals : header.globals = fixture.packet.compiled.indexed.base.globals.length) :
    Admission (CallableIndexedOwnedIndirectCallerProtocol.forget_slots
      (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner header))
      (runtimeContext fixture.packet) (receipt.nested prefixZero globals) :=
  ⟨source_heap_typed fixture atHeader functions owner receipt, receipt.rows⟩

/-- Actual stable owner history and the original current read supply marked readiness. -/
theorem ready_at_entry (prefixZero : owner.key.capturePrefix = 0)
    (globals : header.globals = fixture.packet.compiled.indexed.base.globals.length) :
    (CallableIndexedOwnedNestedCanonicalState.markedProducer (headers := headers) owner header
      (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions)).Ready
      (receipt.nested prefixZero globals) receipt.frameLocation (.state receipt.index) := by
  apply CallableIndexedOwnedNestedCanonicalState.readyAt_of_stableOwner owner header
    (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions) receipt.stable_owner
  exact receipt.body.state.read

end Tests.SourceCoreChosenOrdinaryAcceptedBodyStatePorts
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedCatalogFacts
/-! The actual accepted Header supplies a singleton catalog. Original matcher
and checker interface receipts determine its raw Source signature fields;
deep body typing, native typing and runtime meaning are independent. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreChosenOrdinaryAcceptedCatalogFacts
open Solcore Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader

variable {fixture : AcceptedFixture} {header : ActualHeader fixture}

/-- This list retains the Header's genuine selected and cached compiler slot. -/
def headers (header : ActualHeader fixture) :
    RecursiveNamedCatalog.Inventory fixture.packet.compiled.indexed.ancestry
      (.initial fixture.packet.compiled.compatible.checked)
      (CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed).definitions
      (Program.ofChecked fixture.packet.compiled.sourceProgram) := [header]

theorem header_member : header ∈ headers header := List.mem_singleton_self _

/-- The same accepted hook and target identify the complete original row. -/
theorem header_matches (atHeader : HeaderAt fixture header) :
    CallableNamedMetadata.Matches fixture.packet.named.specialized header.instantiation := by
  have matched := CallableNamedMetadata.matches_of_exact header.target
    (CallableIndexedActualNamedSourceReceipts.header_record fixture.packet.compiled header)
  simpa only [atHeader.named] using matched

/-- The matcher retains length equality even when it permits permutations. -/
theorem substitution_empty (checked : Metadata fixture.packet)
    (atHeader : HeaderAt fixture header) : header.instantiation.parameterSubstitution = [] := by
  have equivalent := (header_matches atHeader).substitution
  rw [checked.substitution] at equivalent
  simp only [SourceCompilationPlan.parameterSubstitutionsEquivalent,
    List.length_nil, List.all_nil, Bool.and_eq_true, beq_iff_eq] at equivalent
  exact List.length_eq_zero_iff.mp equivalent.1.1.symm

theorem header_order (checked : Metadata fixture.packet) (atHeader : HeaderAt fixture header) :
    header.instantiation.parameterSubstitution.map Prod.fst =
      (header.named.specialized.parameterSubstitution.map Prod.fst).reverse := by
  rw [substitution_empty checked atHeader, atHeader.named, checked.substitution]
  rfl

theorem headers_order (checked : Metadata fixture.packet) (atHeader : HeaderAt fixture header) :
    ∀ candidate, candidate ∈ headers header →
      candidate.instantiation.parameterSubstitution.map Prod.fst =
        (candidate.named.specialized.parameterSubstitution.map Prod.fst).reverse := by
  intro candidate member
  have same : candidate = header := List.mem_singleton.mp member
  subst candidate
  exact header_order checked atHeader

/-- These facts concern the actual generic catalog signature and its retained
specialized inferred result. They contain no body typing or execution input. -/
structure SignatureFacts (fixture : AcceptedFixture) (signature : ProgramFunctionSignature) : Prop where
  member : signature ∈ fixture.packet.compiled.sourceProgram.signatures.functions
  declaration : signature.id = fixture.packet.named.specialized.declaration
  parameters : signature.parameterTypes = []
  result : fixture.packet.named.specialized.parameterSubstitution.apply
      (TypeSystem.Ty.productMany signature.returnTypes) =
    fixture.packet.named.specialized.function.inferredBodyType

/-- Original worklist provenance and executable checker header facts supply
raw parameters and result without whole-program body well-formedness. -/
theorem signature_facts (selected : OriginalSelection fixture.packet)
    (checked : Metadata fixture.packet) : ∃ signature, SignatureFacts fixture signature := by
  obtain ⟨request, signature, generic, signatureMember, genericMember, _, accepted⟩ :=
    selected.origin fixture.packet
  have programEq := (SourceCoreUnifiedPreparationCertificates.prepare_fields fixture.packet.compiledAccepted).1
  have catalog := SignatureCatalogWellFormed.ofCheckProgram fixture.packet.checked
  rw [← programEq] at catalog
  have genericMember' := genericMember
  rw [programEq] at genericMember'
  obtain ⟨declared, declaredMember, interface⟩ :=
    checkedFunctionHeaderWellFormed_ofCheckProgram fixture.packet.checked genericMember'
  rw [← programEq] at declaredMember interface
  have identities := RecursiveNamedSpecializationBodyFacts.identities accepted
  have declaredEq : declared = signature := StructuralSubstitution.eq_of_mem_of_mapped_nodup
    catalog.function_ids declaredMember signatureMember
    (interface.declaration_eq.symm.trans identities.1.symm)
  subst declared
  have fields := (CallableCoercionBodyProvenance.specialization_fields accepted).1
  have inputs : fixture.packet.named.specialized.function.typedBody.inputs = [] := checked.inputs
  rw [fields] at inputs
  change generic.typedBody.inputs.map
    (SourceSpecialization.applyBinder fixture.packet.named.specialized.parameterSubstitution) = [] at inputs
  have genericInputs := List.map_eq_nil_iff.mp inputs
  obtain ⟨lexical, extension⟩ := interface.inputs_extend
  have length := extension.length_eq
  rw [genericInputs, List.length_nil] at length
  have parameterTypes : signature.parameterTypes = [] := List.length_eq_zero_iff.mp length.symm
  refine ⟨signature, ⟨signatureMember, identities.1.trans identities.2.2.symm, parameterTypes, ?_⟩⟩
  rw [fields]
  change fixture.packet.named.specialized.parameterSubstitution.apply
    (TypeSystem.Ty.productMany signature.returnTypes) =
    fixture.packet.named.specialized.parameterSubstitution.apply generic.inferredBodyType
  rw [interface.result_type]

/-- Actual signature identity is unique in the catalog checked by checkProgram. -/
theorem signature_at (selected : OriginalSelection fixture.packet) (checked : Metadata fixture.packet)
    (atHeader : HeaderAt fixture header) {signature : ProgramFunctionSignature}
    (member : signature ∈ fixture.packet.compiled.sourceProgram.signatures.functions)
    (declaration : header.instantiation.declaration = signature.id) :
    SignatureFacts fixture signature := by
  obtain ⟨actual, facts⟩ := signature_facts selected checked
  have programEq := (SourceCoreUnifiedPreparationCertificates.prepare_fields fixture.packet.compiledAccepted).1
  have catalog := SignatureCatalogWellFormed.ofCheckProgram fixture.packet.checked
  rw [← programEq] at catalog
  have namedDeclaration := (header_matches atHeader).declaration
  have same : actual = signature := StructuralSubstitution.eq_of_mem_of_mapped_nodup
    catalog.function_ids facts.member member (facts.declaration.trans (namedDeclaration.trans declaration))
  exact same ▸ facts

theorem header_bindings_empty (checked : Metadata fixture.packet) (atHeader : HeaderAt fixture header) :
    header.bindings = [] := atHeader.bindings.trans checked.named_inputs

/-- The actual Header keeps the named compiler context's complete ledger. -/
theorem named_ledger (atHeader : HeaderAt fixture header) :
    (CallableIndexedNamedGeneration.context fixture.packet.compiled.indexed fixture.packet.named).solvedRequirements = header.solved :=
  atHeader.ledger.symm

/-- The receiving context may retain lexical and residual variables. Its
genuine signature catalog equality is the only contextual premise here. -/
theorem source_types_at (selected : OriginalSelection fixture.packet) (checked : Metadata fixture.packet)
    (atHeader : HeaderAt fixture header) (currentContext : SourceSemantics.Context)
    (signatures : currentContext.signatures = fixture.packet.compiled.sourceProgram.signatures) :
    RecursiveNamedCallEvidenceHeads.SourceTypes (headers header) currentContext := by
  refine ⟨?_, ?_, ?_⟩
  · intro candidate member signature signatureMember declaration
    have same : candidate = header := List.mem_singleton.mp member
    subst candidate
    have facts := signature_at selected checked atHeader (signatures ▸ signatureMember) declaration
    rw [facts.parameters, header_bindings_empty checked atHeader]
    rfl
  · intro candidate member signature signatureMember declaration
    have same : candidate = header := List.mem_singleton.mp member
    subst candidate
    have facts := signature_at selected checked atHeader (signatures ▸ signatureMember) declaration
    have actualInstantiation := (header_matches atHeader).canonical
      (by rw [checked.substitution, substitution_empty checked atHeader])
    rw [actualInstantiation]
    change fixture.packet.named.specialized.parameterSubstitution.apply
      (TypeSystem.Ty.productMany signature.returnTypes) = header.function.resultType
    exact facts.result.trans (by simpa only [atHeader.named] using header.agreement.result.symm)
  · intro candidate member
    have same : candidate = header := List.mem_singleton.mp member
    subst candidate
    rw [header_bindings_empty checked atHeader]
    rfl

theorem source_types_at_runtime (selected : OriginalSelection fixture.packet) (checked : Metadata fixture.packet)
    (atHeader : HeaderAt fixture header) :
    RecursiveNamedCallEvidenceHeads.SourceTypes (headers header) (runtimeContext fixture.packet) :=
  source_types_at selected checked atHeader _ rfl

end Tests.SourceCoreChosenOrdinaryAcceptedCatalogFacts
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedHeaderEvidence
/-! The actual successful compilation constructs a Header whose original
prepared Source view has an empty evidence dictionary. The receipt retains
this constructor fact beside HeaderAt for the same Header. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreChosenOrdinaryAcceptedHeaderEvidence
open Solcore Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering Core
open CallableIndexedNamedGeneration
open Tests.SourceCoreChosenOrdinaryAcceptedFixture
open Tests.SourceCoreChosenOrdinaryAcceptedHeader

/-- Retain the original view's evidence field from the actual constructor.
The successful Compilation is eliminated only into this Prop receipt. -/
theorem header_exists_with_evidence (fixture : AcceptedFixture) (selected : OriginalSelection fixture.packet)
    (checked : Metadata fixture.packet) : ∃ header : ActualHeader fixture, HeaderAt fixture header ∧ header.function.evidence = [] := by
  obtain ⟨compilation⟩ := fixture.packet.named_compilation
  let function := RecursiveNamedPreparedSourceFrames.view fixture.packet.compiled.sourceProgram fixture.packet.named compilation.statements
  have frame := source_frame fixture selected checked compilation
  obtain ⟨row, _, prepared⟩ := RecursiveNamedPreparedParameterProjections.cached_preparation
    fixture.packet.compiled fixture.packet.namedSelected
  have agreement := RecursiveNamedPreparedSourceFrames.agreement prepared compilation
  have namedInputs := checked.named_inputs
  have parameters : function.parameters = [] := checked.inputs
  have sameContext : function.context = runtimeContext fixture.packet := checked.view_context compilation.statements
  have extended : MonoBindersExtend function.source.owner function.context function.parameters [] (runtimeContext fixture.packet) := by
    rw [parameters, sameContext]
    exact .nil _
  have valid : CompatibleRuntimeContextValidity.Valid fixture.packet.named.specialized.function.solvedRequirements
      (runtimeContext fixture.packet) function.evidence := by
    refine ⟨rfl, ?_, ?_⟩
    · exact fixture.runtime.source_runtime.requirements
    · have covers := RecursiveNamedPreparedSourceFrames.empty_covers (program := fixture.packet.compiled.sourceProgram) checked.assumptions
      rw [← sameContext]
      exact covers
  have unique : NodeOccurrencesUnique function.source := fixture.runtime.source_runtime.graph.nodeOccurrencesUnique
  have parameterType : fixture.packet.named.signature.parameterType =
      SourceCoreCompatibleCatalog.packTypes (fixture.packet.named.inputs.map Prod.snd) := by
    rw [namedInputs, List.map_nil]
    exact checked.parameter
  let header := RecursiveNamedCatalog.Header.of_dictionary_body
    (values := .initial fixture.packet.compiled.compatible.checked)
    (function := function) (instantiation := CallableNamedMetadata.instantiation fixture.packet.named.specialized)
    (sourceBody := RecursiveNamedSpecializationBodyFacts.bodyInstance fixture.packet.compiled.sourceProgram fixture.packet.named.specialized)
    (frame := frame) (named := fixture.packet.named) (agreement := agreement)
    (ordinaryReturn := checked.ordinary) (ordinaryParameters := by intro binder member; rw [parameters] at member; cases member)
    (target := checked.target) (context := runtimeContext fixture.packet) (types := []) (bindings := fixture.packet.named.inputs)
    (parameters := agreement.parameters) (inputs := agreement.parameters) (extended := extended)
    (solved := fixture.packet.named.specialized.function.solvedRequirements)
    (reasonAt := (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key)
    (readFuel := fixture.packet.compiled.indexed.fuel) (output := fixture.packet.named.signature.resultType)
    (policy := policy fixture)
    (fuel := fixture.packet.compiled.indexed.fuel) (fellThrough := compilation.own.fellThroughReason)
    (escaped := compilation.own.table.escapedReason) (body := compilation.body) (parameterCode := compilation.parameterCode)
    (code := compilation.output) (layouts := fixture.packet.compiled.indexed.layouts)
    (owner := fixture.packet.named.signature.key) (active := []) (globals := fixture.packet.compiled.indexed.base.globals.length)
    (onError := fun error => .sourceAllocation (reprStr error)) (acceptedPrefix := compilation.parametersCompiled)
    (hook := compilation.hook) (definitions_eq := rfl) (registered := CallableIndexedAmbient.frame_registered fixture.packet.compiled.indexed)
    (valid := valid) (unique := unique) (parameterType := parameterType) (resultType := rfl)
    (representation := representation fixture.packet.compiled.indexed) (compiledFuel := fixture.packet.compiled.indexed.fuel)
    (compiled := fixture.packet.compiled.indexed.secondPass) (slot := 0) (selected := fixture.packet.namedSelected)
    (cached := fixture.packet.cached.trans (congrArg some compilation.emitted))
  obtain ⟨parentsEq, ownEq, statementsEq, bodyEq⟩ := fixture.calls.compilation_alignment compilation
  obtain ⟨parametersEq, outputEq⟩ := fixture.tail.compilation_alignment compilation
  refine ⟨header, ?_, rfl⟩
  refine ⟨rfl, rfl, rfl, sameContext, parameters, rfl, bodyEq, parametersEq, outputEq, rfl, rfl,
    fixture.calls.fuel, fixture.calls.fuel, statementsEq, rfl, ?_⟩
  simpa only [header, function, RecursiveNamedPreparedSourceFrames.view, ownEq, statementsEq, bodyEq,
    CallableIndexedNamedGeneration.source, bodyAction, SourceCoreGeneralFunctions.bodyLowererWithRepresentation,
    policy] using fixture.calls.bodyCompiled

/-- The checked fixture supplies the same authentic Header and evidence receipt. -/
theorem header_fixture_with_evidence (given : HeaderFixture) :
    ∃ header : ActualHeader given.fixture,
      HeaderAt given.fixture header ∧ header.function.evidence = [] :=
  header_exists_with_evidence given.fixture given.selected given.checked

end Tests.SourceCoreChosenOrdinaryAcceptedHeaderEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedHeaderRuntimeEvidence
/-! The original successful Header constructor retains its actual global-slot
count and empty evidence alongside HeaderAt. Both equations belong to the same
constructed Header; neither is inferred from an arbitrary HeaderAt receipt. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreChosenOrdinaryAcceptedHeaderRuntimeEvidence
open Solcore Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering Core
open CallableIndexedNamedGeneration
open Tests.SourceCoreChosenOrdinaryAcceptedFixture
open Tests.SourceCoreChosenOrdinaryAcceptedHeader

/-- Runtime fields retained by the same authentic Header constructor. -/
structure RuntimeEvidence (fixture : AcceptedFixture) (header : ActualHeader fixture) : Prop
    extends HeaderAt fixture header where
  evidence : header.function.evidence = []
  globals : header.globals = fixture.packet.compiled.indexed.base.globals.length

/-- Retain actual globals and evidence from the original constructor.
The successful Compilation is eliminated only into this Prop receipt. -/
theorem header_exists_with_runtime (fixture : AcceptedFixture) (selected : OriginalSelection fixture.packet)
    (checked : Metadata fixture.packet) : ∃ header : ActualHeader fixture, RuntimeEvidence fixture header := by
  obtain ⟨compilation⟩ := fixture.packet.named_compilation
  let function := RecursiveNamedPreparedSourceFrames.view fixture.packet.compiled.sourceProgram fixture.packet.named compilation.statements
  have frame := source_frame fixture selected checked compilation
  obtain ⟨row, _, prepared⟩ := RecursiveNamedPreparedParameterProjections.cached_preparation
    fixture.packet.compiled fixture.packet.namedSelected
  have agreement := RecursiveNamedPreparedSourceFrames.agreement prepared compilation
  have namedInputs := checked.named_inputs
  have parameters : function.parameters = [] := checked.inputs
  have sameContext : function.context = runtimeContext fixture.packet := checked.view_context compilation.statements
  have extended : MonoBindersExtend function.source.owner function.context function.parameters [] (runtimeContext fixture.packet) := by
    rw [parameters, sameContext]
    exact .nil _
  have valid : CompatibleRuntimeContextValidity.Valid fixture.packet.named.specialized.function.solvedRequirements
      (runtimeContext fixture.packet) function.evidence := by
    refine ⟨rfl, ?_, ?_⟩
    · exact fixture.runtime.source_runtime.requirements
    · have covers := RecursiveNamedPreparedSourceFrames.empty_covers (program := fixture.packet.compiled.sourceProgram) checked.assumptions
      rw [← sameContext]
      exact covers
  have unique : NodeOccurrencesUnique function.source := fixture.runtime.source_runtime.graph.nodeOccurrencesUnique
  have parameterType : fixture.packet.named.signature.parameterType =
      SourceCoreCompatibleCatalog.packTypes (fixture.packet.named.inputs.map Prod.snd) := by
    rw [namedInputs, List.map_nil]
    exact checked.parameter
  let header := RecursiveNamedCatalog.Header.of_dictionary_body
    (values := .initial fixture.packet.compiled.compatible.checked)
    (function := function) (instantiation := CallableNamedMetadata.instantiation fixture.packet.named.specialized)
    (sourceBody := RecursiveNamedSpecializationBodyFacts.bodyInstance fixture.packet.compiled.sourceProgram fixture.packet.named.specialized)
    (frame := frame) (named := fixture.packet.named) (agreement := agreement)
    (ordinaryReturn := checked.ordinary) (ordinaryParameters := by intro binder member; rw [parameters] at member; cases member)
    (target := checked.target) (context := runtimeContext fixture.packet) (types := []) (bindings := fixture.packet.named.inputs)
    (parameters := agreement.parameters) (inputs := agreement.parameters) (extended := extended)
    (solved := fixture.packet.named.specialized.function.solvedRequirements)
    (reasonAt := (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key)
    (readFuel := fixture.packet.compiled.indexed.fuel) (output := fixture.packet.named.signature.resultType)
    (policy := policy fixture)
    (fuel := fixture.packet.compiled.indexed.fuel) (fellThrough := compilation.own.fellThroughReason)
    (escaped := compilation.own.table.escapedReason) (body := compilation.body) (parameterCode := compilation.parameterCode)
    (code := compilation.output) (layouts := fixture.packet.compiled.indexed.layouts)
    (owner := fixture.packet.named.signature.key) (active := []) (globals := fixture.packet.compiled.indexed.base.globals.length)
    (onError := fun error => .sourceAllocation (reprStr error)) (acceptedPrefix := compilation.parametersCompiled)
    (hook := compilation.hook) (definitions_eq := rfl) (registered := CallableIndexedAmbient.frame_registered fixture.packet.compiled.indexed)
    (valid := valid) (unique := unique) (parameterType := parameterType) (resultType := rfl)
    (representation := representation fixture.packet.compiled.indexed) (compiledFuel := fixture.packet.compiled.indexed.fuel)
    (compiled := fixture.packet.compiled.indexed.secondPass) (slot := 0) (selected := fixture.packet.namedSelected)
    (cached := fixture.packet.cached.trans (congrArg some compilation.emitted))
  obtain ⟨parentsEq, ownEq, statementsEq, bodyEq⟩ := fixture.calls.compilation_alignment compilation
  obtain ⟨parametersEq, outputEq⟩ := fixture.tail.compilation_alignment compilation
  refine ⟨header, { toHeaderAt := ?_, evidence := rfl, globals := rfl }⟩
  refine ⟨rfl, rfl, rfl, sameContext, parameters, rfl, bodyEq, parametersEq, outputEq, rfl, rfl,
    fixture.calls.fuel, fixture.calls.fuel, statementsEq, rfl, ?_⟩
  simpa only [header, function, RecursiveNamedPreparedSourceFrames.view, ownEq, statementsEq, bodyEq,
    CallableIndexedNamedGeneration.source, bodyAction, SourceCoreGeneralFunctions.bodyLowererWithRepresentation,
    policy] using fixture.calls.bodyCompiled

/-- The checked fixture supplies the same authentic Header and runtime facts. -/
theorem header_fixture_with_runtime (given : HeaderFixture) :
    ∃ header : ActualHeader given.fixture,
      RuntimeEvidence given.fixture header :=
  header_exists_with_runtime given.fixture given.selected given.checked

end Tests.SourceCoreChosenOrdinaryAcceptedHeaderRuntimeEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedInitialBodyAdmission
/-! The authentic empty public Source heap and the real singleton named hook
supply admission at the unchanged nested body state. Empty parameter allocation
preserves the original Source heap; hook installation covers every actual row.
No body meaning, whole-program well-formedness or runtime value inverse is used. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreChosenOrdinaryAcceptedInitialBodyAdmission
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader

/-- Finite inversion retains the original empty public heap and Source entry. -/
theorem empty_parameters (fixture : AcceptedFixture) {header : ActualHeader fixture}
    (atHeader : HeaderAt fixture header)
    {before heap : Dynamic.Heap} {arguments : List Dynamic.Value} {environment : Dynamic.Environment}
    (beforeEmpty : before = ⟨[]⟩)
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment heap) :
    arguments = [] ∧ environment = [] ∧ heap = ⟨[]⟩ ∧
      Dynamic.HeapWellTyped (runtimeContext fixture.packet) heap := by
  rw [atHeader.parameters] at allocated
  cases allocated
  subst before
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro cell member
  cases member

section Singleton
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : SourceSemantics.Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {key : CallableIndexedOwnedFunctionValues.Key compiled program}
  {index : ProtectedStateTransition.Index}

/-- The authentic hook updates every row of the actual singleton physical pool. -/
theorem rows_after_singleton_install (first : State headers [key] index)
    (selected : Fin [key].length) {next : NativeFrame} {ghost : GhostFrame} {metadata : Option MetadataState}
    (carried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table next ghost metadata) :
    StableRows (CallableIndexedOwnedFunctionState.install first selected (.stable carried)) := by
  intro row
  have same : row = selected := by
    apply Fin.ext
    have left := row.isLt
    have right := selected.isLt
    simp only [List.length_singleton] at left right
    omega
  subst row
  have current := CallableIndexedAuthorityPool.Pool.install_current first selected selected (.stable carried)
  have history := CallableIndexedAuthorityPool.Pool.install_ghost first selected selected (.stable carried)
  simp only [ite_true] at current history
  refine ⟨metadata, ?_⟩
  change Carries _ _
    ((first.install selected (.stable carried)).rows selected).authority.current
    ((first.install selected (.stable carried)).rows selected).authority.ghost metadata
  rw [current, history]
  exact carried

variable (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey [key])
  (header : CallableIndexedOwnedFunctionValues.Header compiled program)
  {arguments : List Dynamic.Value} {administrative actualContext : Core.Context}
  {actual : Environment} {embedding : Renaming} {frameLocation : Location}
  {current : NativeFrame} {ghost : GhostFrame}
  (first : State headers [key] index)
  (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers owner.key.locations owner.key.capturePrefix functions registry header arguments index.heap
    (index.store.set frameLocation (encode compiled.indexed.ancestry.layout.frame current))
    index.mapping index.world administrative actualContext actual embedding frameLocation current ghost)
  (reached : State headers [key] ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
    entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)

include first in
/-- Actual parameter effects carry every installed row to the same reached pool. -/
theorem rows_at_parameters (physical : frameLocation = owner.key.frameLocation)
    {metadata : Option MetadataState}
    (carried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table current ghost metadata) :
    StableRows reached := by
  have parameterFrame : AdministrativePreserved index.mapping
      (index.store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame current))
      entry.mapping entry.store := by
    simpa only [physical] using entry.frame
  exact StableRows.after_administrative
    (CallableIndexedOwnedFunctionState.install first owner.position (.stable carried)) reached
    (rows_after_singleton_install first owner.position carried) parameterFrame

end Singleton

section Fixture
variable (fixture : AcceptedFixture) {header : ActualHeader fixture}
  (atHeader : HeaderAt fixture header)
  {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.packet.compiled
    (Program.ofChecked fixture.packet.compiled.sourceProgram))}
  {key : CallableIndexedOwnedFunctionValues.Key fixture.packet.compiled
    (Program.ofChecked fixture.packet.compiled.sourceProgram)}
  (functions : FunctionModel fixture.packet.compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey [key])
  {index : ProtectedStateTransition.Index} (first : State headers [key] index)
  {arguments : List Dynamic.Value} {administrative actualContext : Core.Context}
  {actual : Environment} {embedding : Renaming} {frameLocation : Location}
  {current : NativeFrame} {ghost : GhostFrame}
  (entry : BodyState (prepared := fixture.packet.compiled.indexed.ancestry)
    (values := .initial fixture.packet.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed)
    headers owner.key.locations owner.key.capturePrefix functions registry header arguments index.heap
    (index.store.set frameLocation (encode fixture.packet.compiled.indexed.ancestry.layout.frame current))
    index.mapping index.world administrative actualContext actual embedding frameLocation current ghost)
  (reached : State headers [key] ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
    entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)

include atHeader first in
/-- The actual principal packet accompanies the same deeply typed, all-row pool. -/
theorem nested_admission (beforeEmpty : index.heap = ⟨[]⟩)
    (prefixZero : owner.key.capturePrefix = 0)
    (globals : header.globals = fixture.packet.compiled.indexed.base.globals.length)
    (allowed : CallableIndexedOwnedNamedCanonicalEntries.condition functions owner header entry) :
    Admission (CallableIndexedOwnedIndirectCallerProtocol.forget_slots
      (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner header))
      (runtimeContext fixture.packet)
      (CallableIndexedOwnedNamedCanonicalEntries.wrap functions owner header entry reached prefixZero globals allowed) := by
  obtain ⟨_, _, _, heapTyped⟩ := empty_parameters fixture atHeader beforeEmpty entry.allocation
  have rows := rows_at_parameters functions owner header first entry reached allowed.1 allowed.2
  exact ⟨heapTyped, rows⟩

end Fixture
end Tests.SourceCoreChosenOrdinaryAcceptedInitialBodyAdmission
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedPublicBootstrapReceipt
/-! This executable receipt retains one original public preparation and one
bootstrap completion for the unchanged accepted fixture. It identifies the
actual initialized store without asserting Source body or Session semantics. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
namespace Tests.SourceCoreChosenOrdinaryAcceptedPublicBootstrapReceipt
open Solcore Frontend Core SourceSemantics.CoreLowering

/-- The actual Recipe and its acceptance belong to this same fixture packet.
Only the finite list length is checked executably. -/
structure PublicRecipeReceipt (fixture : SourceCoreChosenOrdinaryAcceptedFixture.AcceptedFixture) where
  recipe : SourceCoreIndexedSession.Recipe
  accepted : SourceCoreIndexedSession.Recipe.prepare fixture.packet.compiled = .ok recipe
  one_named : fixture.packet.compiled.indexed.base.functions.length = 1

def prepare_public (fixture : SourceCoreChosenOrdinaryAcceptedFixture.AcceptedFixture) :
    Except String (PublicRecipeReceipt fixture) := do
  let prepared ← match accepted : SourceCoreIndexedSession.Recipe.prepare fixture.packet.compiled with
    | .error error => throw s!"public Recipe.prepare: {reprStr error}"
    | .ok recipe => pure (⟨recipe, accepted⟩ :
        {r // SourceCoreIndexedSession.Recipe.prepare fixture.packet.compiled = .ok r})
  if one : fixture.packet.compiled.indexed.base.functions.length = 1 then
    pure ⟨prepared.val, prepared.property, one⟩
  else throw "the actual accepted fixture has more than one named row"

theorem compiled_eq {fixture : SourceCoreChosenOrdinaryAcceptedFixture.AcceptedFixture} (prepared : PublicRecipeReceipt fixture) :
    prepared.recipe.compiled = fixture.packet.compiled :=
  SourceCoreIndexedSession.Recipe.prepare_compiled prepared.accepted

/-- The authentic selected row and length check identify the whole list; no
executable equality of proof-bearing named records is used. -/
theorem functions_singleton {fixture : SourceCoreChosenOrdinaryAcceptedFixture.AcceptedFixture}
    (prepared : PublicRecipeReceipt fixture) :
    fixture.packet.compiled.indexed.base.functions = [fixture.packet.named] := by
  have one := prepared.one_named
  have selected := fixture.packet.namedSelected
  cases rows : fixture.packet.compiled.indexed.base.functions with
  | nil => simp [rows] at one
  | cons named rest =>
    cases rest with
    | nil =>
      simp [rows] at selected
      simp [selected]
    | cons next tail => simp [rows] at one

/-- A successful original machine completion, at precisely this Recipe. -/
structure CompletedBootstrap {fixture : SourceCoreChosenOrdinaryAcceptedFixture.AcceptedFixture}
    (prepared : PublicRecipeReceipt fixture) (fuel : Nat) where
  value : Value
  store : Store
  completed : runStateful fuel (.initial prepared.recipe.bootstrap [] []) = .done value store

def complete_bootstrap {fixture : SourceCoreChosenOrdinaryAcceptedFixture.AcceptedFixture}
    (prepared : PublicRecipeReceipt fixture) (fuel : Nat) :
    Except String (CompletedBootstrap prepared fuel) :=
  match completed : runStateful fuel (.initial prepared.recipe.bootstrap [] []) with
  | .done value store => .ok ⟨value, store, completed⟩
  | .outOfFuel _ => .error s!"public bootstrap exhausted fuel {fuel}"
  | .fault error _ => .error s!"public bootstrap fault: {reprStr error}"

/-- The observed completion is the original exact initialization; this uses
its retained preparation equation and never runs either producer again. -/
theorem completed_store {fixture : SourceCoreChosenOrdinaryAcceptedFixture.AcceptedFixture}
    {prepared : PublicRecipeReceipt fixture} {fuel : Nat}
    (completed : CompletedBootstrap prepared fuel) :
    completed.value = .inRight .word .unit ∧
      completed.store = RecursiveNamedCatalogPreparedInitialization.store fixture.packet.compiled :=
  RecursiveNamedCatalogPreparedInitialization.completed_store prepared.accepted completed.completed

def bootstrapFuel : Nat := 10000

structure PublicBootstrapFixture where
  fixture : SourceCoreChosenOrdinaryAcceptedFixture.AcceptedFixture
  prepared : PublicRecipeReceipt fixture
  completed : CompletedBootstrap prepared bootstrapFuel

/-- Runs the unchanged fixture once, public preparation once and the original
bootstrap machine once. Failed actions retain their actual error. -/
def accepted_public_fixture : Except String PublicBootstrapFixture := do
  let fixture ← SourceCoreChosenOrdinaryAcceptedFixture.acceptedFixture
  let prepared ← prepare_public fixture
  let completed ← complete_bootstrap prepared bootstrapFuel
  pure ⟨fixture, prepared, completed⟩

def run : IO Unit := do
  match accepted_public_fixture with
  | .error error => throw (IO.userError error)
  | .ok actual =>
    IO.println s!"accepted public bootstrap: one original Recipe, one named row, original machine completed at fuel {bootstrapFuel}; initialized store has {actual.completed.store.length} cells"

end Tests.SourceCoreChosenOrdinaryAcceptedPublicBootstrapReceipt
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedStaticInventory
/-! Finite inventory checks use the unchanged accepted fixture Source. Actual
lookup receipts identify every retained node. Diagnostic typing follows by
absence; builtin row profiles keep original numeric and local metadata. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Tests.SourceCoreChosenOrdinaryAcceptedStaticInventory
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedNamedGeneration SourceCoreChosenOrdinaryAcceptedFixture

/-- The allowed ids name the actual Graph and ParentRows records. -/
def checkInventory (packet : Packet) : Bool :=
  (source packet.named).nodes.all fun
    | .statement node => decide (node.id = statementId packet 0 ∨
        node.id = statementId packet 2 ∨ node.id = statementId packet 4)
    | .expression node => decide (node.id = expressionId packet 1 ∨
        node.id = expressionId packet 3 ∨ node.id = expressionId packet 5 ∨
        node.id = expressionId packet 6 ∨ node.id = expressionId packet 7 ∨
        node.id = expressionId packet 8 ∨ node.id = expressionId packet 9)

structure Inventory (fixture : AcceptedFixture) : Prop where
  nodes : checkInventory fixture.packet = true
  contracts : fixture.packet.compiled.compatible.checked.catalog.callableContracts = true
  parameterType : fixture.packet.named.signature.parameterType = .unit
  resultType : fixture.packet.named.signature.resultType = .word

def inventory (fixture : AcceptedFixture) : Except String (PLift (Inventory fixture)) := do
  if nodes : checkInventory fixture.packet = true then
    if metadata : fixture.packet.compiled.compatible.checked.catalog.callableContracts = true ∧
        fixture.packet.named.signature.parameterType = .unit ∧ fixture.packet.named.signature.resultType = .word then
      pure ⟨⟨nodes, metadata.1, metadata.2.1, metadata.2.2⟩⟩
    else throw "actual callable contract or named signature differs"
  else throw "actual Source node inventory differs"

variable {fixture : AcceptedFixture}

theorem Inventory.statement_ids (given : Inventory fixture) {id : StatementId} {node : StatementNode}
    (found : (source fixture.packet.named).lookupStatement? id = some node) :
    id = statementId fixture.packet 0 ∨ id = statementId fixture.packet 2 ∨ id = statementId fixture.packet 4 := by
  have contains := lookupStatement?_sound found
  have checked := List.all_eq_true.mp given.nodes (.statement node) contains.1
  change decide (node.id = statementId fixture.packet 0 ∨ node.id = statementId fixture.packet 2 ∨
    node.id = statementId fixture.packet 4) = true at checked
  simpa only [contains.2] using of_decide_eq_true checked

theorem Inventory.expression_ids (given : Inventory fixture) {id : ExpressionId} {node : ExpressionNode}
    (found : (source fixture.packet.named).lookupExpression? id = some node) :
    id = expressionId fixture.packet 1 ∨ id = expressionId fixture.packet 3 ∨ id = expressionId fixture.packet 5 ∨
    id = expressionId fixture.packet 6 ∨ id = expressionId fixture.packet 7 ∨
    id = expressionId fixture.packet 8 ∨ id = expressionId fixture.packet 9 := by
  have contains := lookupExpression?_sound found
  have checked := List.all_eq_true.mp given.nodes (.expression node) contains.1
  change decide (node.id = expressionId fixture.packet 1 ∨ node.id = expressionId fixture.packet 3 ∨
    node.id = expressionId fixture.packet 5 ∨ node.id = expressionId fixture.packet 6 ∨
    node.id = expressionId fixture.packet 7 ∨ node.id = expressionId fixture.packet 8 ∨
    node.id = expressionId fixture.packet 9) = true at checked
  simpa only [contains.2] using of_decide_eq_true checked

/-- Full row equality uses genuine lookup receipts, including raw metadata. -/
theorem Inventory.statements (given : Inventory fixture) {id : StatementId} {node : StatementNode}
    (found : (source fixture.packet.named).lookupStatement? id = some node) :
    node = fixture.graph.initialized ∨ node = fixture.graph.returned ∨ node = fixture.graph.outerReturn := by
  rcases given.statement_ids found with rfl | rfl | rfl
  · exact .inl (Option.some.inj (found.symm.trans fixture.graph.initializedFound))
  · exact .inr (.inl (Option.some.inj (found.symm.trans fixture.graph.returnedFound)))
  · exact .inr (.inr (Option.some.inj (found.symm.trans fixture.graph.outerReturnFound)))

theorem Inventory.expressions (given : Inventory fixture) {id : ExpressionId} {node : ExpressionNode}
    (found : (source fixture.packet.named).lookupExpression? id = some node) :
    node = fixture.graph.lambdaNode ∨ node = fixture.graph.literal ∨ node = fixture.graph.parent ∨
    node = fixture.graph.argument ∨ node = fixture.parentRows.left ∨ node = fixture.parentRows.right ∨ node = fixture.graph.callee := by
  rcases given.expression_ids found with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inl (Option.some.inj (found.symm.trans fixture.graph.lambdaFound))
  · exact .inr (.inl (Option.some.inj (found.symm.trans fixture.graph.literalFound)))
  · exact .inr (.inr (.inl (Option.some.inj (found.symm.trans fixture.graph.parentFound))))
  · exact .inr (.inr (.inr (.inl (Option.some.inj (found.symm.trans fixture.graph.argumentFound)))))
  · exact .inr (.inr (.inr (.inr (.inl (Option.some.inj (found.symm.trans fixture.parentRows.leftFound))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl (Option.some.inj (found.symm.trans fixture.parentRows.rightFound)))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (Option.some.inj (found.symm.trans fixture.graph.calleeFound)))))))

private theorem no_statement_forms (given : Inventory fixture) {id : StatementId} {node : StatementNode}
    (found : (source fixture.packet.named).lookupStatement? id = some node) :
    (∀ assignment, node.form ≠ .assignBitNot assignment) ∧
    (∀ assignment operator rhs, node.form ≠ .assignValue assignment operator rhs) ∧
    (∀ initial condition post body, node.form ≠ .forLoop initial condition post body) := by
  rcases given.statements found with rfl | rfl | rfl <;>
    simp [fixture.graph.initializedForm, fixture.graph.returnedForm, fixture.graph.outerReturnForm]

/-- No unary statement or for-header occurrence exists in this full Source. -/
theorem Inventory.unary_typed (given : Inventory fixture) : EmittedDiagnosticTokenPlan.UnaryTyped (source fixture.packet.named) := by
  intro site assignment origin
  cases origin with
  | statement found form => exact ((no_statement_forms given found).1 _ form).elim
  | header found form _ => exact ((no_statement_forms given found).2.2 _ _ _ _ form).elim

/-- No assignment statement or for-header occurrence exists in this full Source. -/
theorem Inventory.operands_typed (given : Inventory fixture) : AssignmentDiagnosticOrigins.OperandsTyped (source fixture.packet.named) := by
  intro site assignment operator rhs origin
  cases origin with
  | statement found form => exact ((no_statement_forms given found).2.1 _ _ _ form).elim
  | header found form _ => exact ((no_statement_forms given found).2.2 _ _ _ _ form).elim

theorem Inventory.typing (given : Inventory fixture) :
    EmittedDiagnosticTokenPlan.UnaryTyped (source fixture.packet.named) ∧
    AssignmentDiagnosticOrigins.OperandsTyped (source fixture.packet.named) := ⟨given.unary_typed, given.operands_typed⟩

/-- Genuine full inventory excludes every constructor, at any static context. -/
theorem Inventory.constructor_law (given : Inventory fixture) (context : SourceSemantics.Context)
    (allowed : ExpressionId → Prop) : CompatibleExpressionInstantiationLaws.ConstructorLaw (source fixture.packet.named) context allowed := by
  intro id node instantiation arguments _allowed found form _valid
  rcases given.expressions found with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [fixture.graph.lambdaForm, fixture.graph.literalForm, fixture.graph.parentForm,
      fixture.graph.argumentForm, fixture.parentRows.leftForm, fixture.parentRows.rightForm, fixture.graph.calleeForm] at form

/-- Local references are the original nongeneralized callee row. -/
theorem Inventory.reference_profile (given : Inventory fixture) {id : ExpressionId} {node : ExpressionNode}
    {name : String} {binder : Resolved.LocalId} (found : (source fixture.packet.named).lookupExpression? id = some node)
    (form : node.form = .reference name (.local binder)) :
    fixture.packet.compiled.indexed.base.locals.bindings.any (fun binding =>
      decide (binding.caller = fixture.packet.named.signature.key ∧ binding.binder.id = binder)) = false := by
  rcases given.expressions found with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try simp [fixture.graph.lambdaForm, fixture.graph.literalForm, fixture.graph.parentForm,
    fixture.graph.argumentForm, fixture.parentRows.leftForm, fixture.parentRows.rightForm] at form
  have same := ExpressionForm.reference.inj (fixture.graph.calleeForm.symm.trans form)
  have binderEq := ReferenceResolution.local.inj same.2
  rw [← binderEq]
  exact fixture.parentRows.generalized

/-- Only the lambda and indirect call are outside the builtin grammar. -/
private def extraRoot : ExpressionForm → Bool
  | .lambda _ _ _ => true
  | .call _ _ (.indirect _) => true
  | _ => false

private theorem atomic_root {form : ExpressionForm}
    (atomic : CompatibleExpressionLiterals.Atomic form) : extraRoot form = false := by
  cases atomic <;> rfl

private theorem product_root {view : TypedSource} {id : ExpressionId}
    (tree : CompatibleExpressionProducts.Syntax view id) :
    ∃ node, view.lookupExpression? id = some node ∧ extraRoot node.form = false := by
  cases tree with
  | literal found atomic => exact ⟨_, found, atomic_root atomic⟩
  | read found form => exact ⟨_, found, by rw [form]; rfl⟩
  | group found form _ => exact ⟨_, found, by rw [form]; rfl⟩
  | pair found form _ _ => exact ⟨_, found, by rw [form]; rfl⟩

private theorem primitive_root {view : TypedSource} {id : ExpressionId}
    (tree : CompatibleExpressionPrimitives.Syntax view id) :
    ∃ node, view.lookupExpression? id = some node ∧ extraRoot node.form = false := by
  cases tree with
  | product child => exact product_root child
  | group found form _ => exact ⟨_, found, by rw [form]; rfl⟩
  | pair found form _ _ => exact ⟨_, found, by rw [form]; rfl⟩
  | unary found form _ => exact ⟨_, found, by rw [form]; rfl⟩
  | binary found form _ _ => exact ⟨_, found, by rw [form]; rfl⟩

private theorem conditional_root {view : TypedSource} {id : ExpressionId}
    (tree : CompatibleExpressionConditionals.Syntax view id) :
    ∃ node, view.lookupExpression? id = some node ∧ extraRoot node.form = false := by
  cases tree with
  | primitive child => exact primitive_root child
  | group found form _ => exact ⟨_, found, by rw [form]; rfl⟩
  | pair found form _ _ => exact ⟨_, found, by rw [form]; rfl⟩
  | unary found form _ => exact ⟨_, found, by rw [form]; rfl⟩
  | binary found form _ _ => exact ⟨_, found, by rw [form]; rfl⟩
  | conditional found form _ _ _ => exact ⟨_, found, by rw [form]; rfl⟩

private theorem constructor_root {view : TypedSource} {id : ExpressionId}
    (tree : CompatibleExpressionConstructors.Syntax view id) :
    ∃ node, view.lookupExpression? id = some node ∧ extraRoot node.form = false := by
  cases tree with
  | fragment child => exact conditional_root child
  | constructor found form _ => exact ⟨_, found, by rw [form]; rfl⟩

private theorem member_root {view : TypedSource} {id : ExpressionId}
    (tree : CompatibleExpressionMembers.Syntax view id) :
    ∃ node, view.lookupExpression? id = some node ∧ extraRoot node.form = false := by
  cases tree with
  | fragment child => exact constructor_root child
  | member found form _ => exact ⟨_, found, by rw [form]; rfl⟩

private theorem recursive_root {view : TypedSource} {id : ExpressionId}
    (tree : CompatibleExpressionRecursive.Syntax view id) :
    ∃ node, view.lookupExpression? id = some node ∧ extraRoot node.form = false := by
  cases tree with
  | fragment child => exact member_root child
  | group found form _ => exact ⟨_, found, by rw [form]; rfl⟩
  | pair found form _ _ => exact ⟨_, found, by rw [form]; rfl⟩
  | unary found form _ => exact ⟨_, found, by rw [form]; rfl⟩
  | binary found form _ _ => exact ⟨_, found, by rw [form]; rfl⟩
  | conditional found form _ _ _ => exact ⟨_, found, by rw [form]; rfl⟩
  | constructor found form _ => exact ⟨_, found, by rw [form]; rfl⟩
  | member found form _ => exact ⟨_, found, by rw [form]; rfl⟩

private theorem general_root {view : TypedSource} {id : ExpressionId}
    (tree : CompatibleExpressionGeneral.Syntax view id) :
    ∃ node, view.lookupExpression? id = some node ∧ extraRoot node.form = false := by
  cases tree with
  | fragment child => exact recursive_root child
  | proxy found form => exact ⟨_, found, by rw [form]; rfl⟩
  | group found form _ => exact ⟨_, found, by rw [form]; rfl⟩
  | pair found form _ _ => exact ⟨_, found, by rw [form]; rfl⟩
  | unary found form _ => exact ⟨_, found, by rw [form]; rfl⟩
  | binary found form _ _ => exact ⟨_, found, by rw [form]; rfl⟩
  | conditional found form _ _ _ => exact ⟨_, found, by rw [form]; rfl⟩
  | constructor found form _ => exact ⟨_, found, by rw [form]; rfl⟩
  | member found form _ => exact ⟨_, found, by rw [form]; rfl⟩
  | index found form _ _ _ => exact ⟨_, found, by rw [form]; rfl⟩

private theorem builtin_root {view : TypedSource} {id : ExpressionId}
    (tree : CompatibleExpressionBuiltins.Syntax view id) :
    ∃ node, view.lookupExpression? id = some node ∧ extraRoot node.form = false := by
  cases tree with
  | fragment child => exact general_root child
  | proxy found form => exact ⟨_, found, by rw [form]; rfl⟩
  | group found form _ => exact ⟨_, found, by rw [form]; rfl⟩
  | pair found form _ _ => exact ⟨_, found, by rw [form]; rfl⟩
  | unary found form _ => exact ⟨_, found, by rw [form]; rfl⟩
  | binary found form _ _ => exact ⟨_, found, by rw [form]; rfl⟩
  | conditional found form _ _ _ => exact ⟨_, found, by rw [form]; rfl⟩
  | constructor found form _ => exact ⟨_, found, by rw [form]; rfl⟩
  | member found form _ => exact ⟨_, found, by rw [form]; rfl⟩
  | index found form _ _ _ => exact ⟨_, found, by rw [form]; rfl⟩
  | builtin found form _ => exact ⟨_, found, by rw [form]; rfl⟩

/-- Every actual builtin row is one of the retained numeric/read/pair rows.
This finite root-form inversion never visits semantic children. -/
theorem Inventory.builtin_ids (given : Inventory fixture) {id : ExpressionId}
    (tree : CompatibleExpressionBuiltins.Syntax (source fixture.packet.named) id) :
    id = expressionId fixture.packet 3 ∨ id = expressionId fixture.packet 6 ∨
    id = expressionId fixture.packet 7 ∨ id = expressionId fixture.packet 8 ∨ id = expressionId fixture.packet 9 := by
  obtain ⟨node, found, ordinary⟩ := builtin_root tree
  rcases given.expression_ids found with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have same := Option.some.inj (found.symm.trans fixture.graph.lambdaFound)
    rw [same, fixture.graph.lambdaForm] at ordinary
    cases ordinary
  · exact .inl rfl
  · have same := Option.some.inj (found.symm.trans fixture.graph.parentFound)
    rw [same, fixture.graph.parentForm] at ordinary
    cases ordinary
  · exact .inr (.inl rfl)
  · exact .inr (.inr (.inl rfl))
  · exact .inr (.inr (.inr (.inl rfl)))
  · exact .inr (.inr (.inr (.inr rfl)))

theorem Inventory.fragment_coercions (given : Inventory fixture) {id : ExpressionId} {node : ExpressionNode}
    (tree : CompatibleExpressionBuiltins.Syntax (source fixture.packet.named) id)
    (found : (source fixture.packet.named).lookupExpression? id = some node) : node.coercions = [] := by
  rcases given.builtin_ids tree with rfl | rfl | rfl | rfl | rfl
  · have same := Option.some.inj (found.symm.trans fixture.graph.literalFound)
    exact same ▸ fixture.graph.literalCoercions
  · have same := Option.some.inj (found.symm.trans fixture.graph.argumentFound)
    exact same ▸ fixture.parentRows.argumentCoercions
  · have same := Option.some.inj (found.symm.trans fixture.parentRows.leftFound)
    exact same ▸ fixture.parentRows.leftCoercions
  · have same := Option.some.inj (found.symm.trans fixture.parentRows.rightFound)
    exact same ▸ fixture.parentRows.rightCoercions
  · have same := Option.some.inj (found.symm.trans fixture.graph.calleeFound)
    exact same ▸ fixture.parentRows.calleeCoercions

/-- The three genuine ordinary forms retain the original contextual read and
special callback, including its literal initializer and evidence gates. -/
theorem ordinary_policy {packet : Packet}
    {compilation : Compilation packet.compiled.indexed packet.named
      (effectiveDiagnostics packet.compiled packet.diagnostics) packet.namedCode}
    {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {rootLowered : SourceCoreBasic.LoweredExpr}
    (root : CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt
      (compiled := packet.compiled) packet.named (effectiveDiagnostics packet.compiled packet.diagnostics)
      packet.namedCode compilation rootFuel rootSource rootScope rootId
      ((effectiveDiagnostics packet.compiled packet.diagnostics).reasonAt packet.named.signature.key) rootLowered)
    {childScope : SourceCoreLocalCell.Scope} {childId : ExpressionId} {node : ExpressionNode}
    {owned : List RequirementId}
    (found : (source packet.named).lookupExpression? childId = some node)
    (shape : (∃ name binder, node.form = .reference name (.local binder) ∧
        packet.compiled.indexed.base.locals.bindings.any (fun binding =>
          decide (binding.caller = packet.named.signature.key ∧ binding.binder.id = binder)) = false) ∨
      (∃ ids, node.form = .tuple ids) ∨
      (∃ literal resolution, node.form = .integerLiteral literal resolution))
    (ownedRequirements : SourceCompilationPlan.ordinaryOwnedRequirements? node = some owned)
    (coercions : node.coercions = [])
    (requirements : node.requirements = [] ∨ ∃ literal resolution, node.form = .integerLiteral literal resolution)
    (ordinary : packet.compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = packet.named.signature.key ∧ binding.initializer = childId)) = none) :
    CallableIndexedOwnedContextualCompilerPolicyProfiles.PointwiseFor root
      (source packet.named) childScope childId
      ((effectiveDiagnostics packet.compiled packet.diagnostics).reasonAt packet.named.signature.key) := by
  have owner : (context packet.compiled.indexed packet.named).owner = packet.named.signature.key := rfl
  have sameSource : SourceCoreGeneralFunctions.contextualSource packet.compiled.indexed.base.sourceProgram
      (context packet.compiled.indexed packet.named).plan packet.compiled.indexed.base.locals
      (context packet.compiled.indexed packet.named).owner none (source packet.named) childId = .ok (source packet.named) := by
    rcases shape with ⟨name, binder, form, generalized⟩ | ⟨ids, form⟩ | ⟨literal, resolution, form⟩
    · simp only [SourceCoreGeneralFunctions.contextualSource, found, bind, Except.bind, pure, Except.pure, form, owner, generalized, Bool.false_eq_true, ↓reduceIte]
    · simp [SourceCoreGeneralFunctions.contextualSource, found, form]
    · simp [SourceCoreGeneralFunctions.contextualSource, found, form]
  constructor
  · rw [root.selected.readExpression]
    simp only [sameSource, bind, Except.bind]
    rw [CallableIndexedOwnedIndirectCompilerPolicyInputs.representation_read (compiled := packet.compiled) packet.named]
  · intro child budget
    rw [root.selected.special_eq, root.selected.special_body]
    have evidenceNone : SourceCoreEvidence.lowerWithProjector packet.compiled.indexed.base.sourceProgram
        ((representation packet.compiled.indexed).atContext packet.named.signature.key []).expressions.projectType
        packet.named.specialized (context packet.compiled.indexed packet.named) child budget
        (source packet.named) childScope childId
        ((effectiveDiagnostics packet.compiled packet.diagnostics).reasonAt packet.named.signature.key)
        (SourceCoreGeneralFunctions.callablePolicy packet.compiled.indexed.base.callableContext []) = .ok none := by
      rcases requirements with empty | ⟨literal, resolution, form⟩
      · rcases shape with ⟨name, binder, form, _generalized⟩ | ⟨ids, form⟩ | ⟨literal, resolution, form⟩ <;>
          simp [SourceCoreEvidence.lowerWithProjector, found, form, ownedRequirements, coercions, empty]
      · simp [SourceCoreEvidence.lowerWithProjector, found, form, ownedRequirements, coercions]
    simp only [bind, Except.bind]
    rw [sameSource]
    simp only [found, pure, Except.pure, owner, ordinary, Option.filter_none, evidenceNone]
    rcases shape with ⟨name, binder, form, generalized⟩ | ⟨ids, form⟩ | ⟨literal, resolution, form⟩
    · simp only [form, generalized, Bool.false_eq_true, ↓reduceIte]
    · simp only [form]
    · simp only [form]

/-- Whole builtin policy fields follow from actual finite row profiles. The
root selector is supplied once by the original initializer acceptance. -/
theorem Inventory.builtin_policy (given : Inventory fixture)
    {compilation : Compilation fixture.packet.compiled.indexed fixture.packet.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
    {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {rootLowered : SourceCoreBasic.LoweredExpr}
    (root : CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt
      (compiled := fixture.packet.compiled) fixture.packet.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode compilation
      rootFuel rootSource rootScope rootId
      ((effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key) rootLowered)
    (childScope : SourceCoreLocalCell.Scope) {id : ExpressionId}
    (tree : CompatibleExpressionBuiltins.Syntax (source fixture.packet.named) id) :
    CallableIndexedOwnedContextualCompilerPolicyProfiles.PointwiseFor root
      (source fixture.packet.named) childScope id
      ((effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key) := by
  have emptyOwned (node : ExpressionNode) (requirements : node.requirements = []) (coercions : node.coercions = []) :
      SourceCompilationPlan.ordinaryOwnedRequirements? node = some [] := by
    unfold SourceCompilationPlan.ordinaryOwnedRequirements?
    rw [requirements, coercions]
    rfl
  rcases given.builtin_ids tree with rfl | rfl | rfl | rfl | rfl
  · exact ordinary_policy root fixture.graph.literalFound
      (.inr (.inr ⟨_, _, fixture.graph.literalForm⟩)) fixture.graph.literalOwned fixture.graph.literalCoercions
      (.inr ⟨_, _, fixture.graph.literalForm⟩) fixture.calls.literalOrdinary
  · exact ordinary_policy root fixture.graph.argumentFound (.inr (.inl ⟨_, fixture.graph.argumentForm⟩))
      (emptyOwned _ fixture.parentRows.argumentRequirements fixture.parentRows.argumentCoercions)
      fixture.parentRows.argumentCoercions (.inl fixture.parentRows.argumentRequirements) fixture.parentRows.argumentOrdinary
  · exact ordinary_policy root fixture.parentRows.leftFound (.inr (.inr ⟨_, _, fixture.parentRows.leftForm⟩))
      fixture.parentRows.leftOwned fixture.parentRows.leftCoercions
      (.inr ⟨_, _, fixture.parentRows.leftForm⟩) fixture.parentRows.leftOrdinary
  · exact ordinary_policy root fixture.parentRows.rightFound (.inr (.inr ⟨_, _, fixture.parentRows.rightForm⟩))
      fixture.parentRows.rightOwned fixture.parentRows.rightCoercions
      (.inr ⟨_, _, fixture.parentRows.rightForm⟩) fixture.parentRows.rightOrdinary
  · exact ordinary_policy root fixture.graph.calleeFound (.inl ⟨_, _, fixture.graph.calleeForm, fixture.parentRows.generalized⟩)
      (emptyOwned _ fixture.parentRows.calleeRequirements fixture.parentRows.calleeCoercions)
      fixture.parentRows.calleeCoercions (.inl fixture.parentRows.calleeRequirements) fixture.parentRows.calleeOrdinary

/-- Execute actual full inventory and signature checks over the unchanged
compiler fixture; the sound static facts above remain kernel proofs. -/
def run : IO Unit := do
  match acceptedFixture with
  | .error error => throw (IO.userError error)
  | .ok fixture =>
    match inventory fixture with
    | .error error => throw (IO.userError error)
    | .ok _ => IO.println "accepted static inventory: complete Source nodes, genuine contract/signature and diagnostic/builtin profiles checked"

end Tests.SourceCoreChosenOrdinaryAcceptedStaticInventory
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedLiteralDomainGlobals
/-! Actual Header and inventory receipts populate the literal body's static
compiler domain. The same supplied root policy and current context are retained. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreChosenOrdinaryAcceptedLiteralDomainGlobals
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
open CallableIndexedOwnedContextualLambdaSourceDiagnostics
open CallableIndexedOwnedLiteralReturnSiteShells
open CallableIndexedOwnedLiteralPlaceDiagnosticShells

private def transport_root
    {compiled : SourceCoreUnifiedCompilation.Compiled} {named target : Named}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation compiled.indexed named diagnostics namedCode}
    {fuel : Nat} {rootSource : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (root : CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt
      (compiled := compiled) named diagnostics namedCode compilation fuel rootSource scope id reasonAt lowered)
    (same : named = target) :=
  Eq.rec (motive := fun actual (identity : named = actual) =>
    CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt
      (compiled := compiled) actual diagnostics namedCode (identity ▸ compilation)
      fuel rootSource scope id reasonAt lowered) root same

private theorem transport_policy
    {compiled : SourceCoreUnifiedCompilation.Compiled} {named target : Named}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation compiled.indexed named diagnostics namedCode}
    {fuel : Nat} {rootSource : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (root : CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt
      (compiled := compiled) named diagnostics namedCode compilation fuel rootSource scope id reasonAt lowered)
    (same : named = target) :
    (transport_root root same).selected.policy = root.selected.policy := by
  cases same
  rfl

variable (fixture : AcceptedFixture) {caller : ActualHeader fixture}
    (atHeader : HeaderAt fixture caller)
    (selected : OriginalSelection fixture.packet) (checked : Metadata fixture.packet)
    (inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory fixture)
    {compilation : Compilation fixture.packet.compiled.indexed caller.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
    {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {rootLowered : SourceCoreBasic.LoweredExpr}
    (root : LiteralRootReceipt (compiled := fixture.packet.compiled) caller.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode compilation
      rootFuel rootSource rootScope rootId
      ((effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key)
      rootLowered)

include atHeader selected checked inventory in
/-- The actual catalog and complete builtin inventory supply every global field.
Lexical variables and residual mode remain those of the supplied current context. -/
theorem globals_at (currentContext : SourceSemantics.Context) (currentScope : SourceCoreLocalCell.Scope)
    (signatures : currentContext.signatures = fixture.packet.compiled.sourceProgram.signatures) :
    LiteralDomainGlobals root currentContext currentScope
      (SourceCoreChosenOrdinaryAcceptedCatalogFacts.headers caller) := by
  let originalRoot := transport_root root.root atHeader.named
  have samePolicy := transport_policy root.root atHeader.named
  have sameSource : source caller.named = source fixture.packet.named := congrArg source atHeader.named
  have sameContext : context fixture.packet.compiled.indexed caller.named =
      context fixture.packet.compiled.indexed fixture.packet.named :=
    congrArg (context fixture.packet.compiled.indexed) atHeader.named
  refine {
    namedLedger := by simpa only [atHeader.named] using SourceCoreChosenOrdinaryAcceptedCatalogFacts.named_ledger atHeader
    headerOrder := SourceCoreChosenOrdinaryAcceptedCatalogFacts.headers_order checked atHeader
    sourceTypes := SourceCoreChosenOrdinaryAcceptedCatalogFacts.source_types_at selected checked atHeader
      currentContext signatures
    fragmentValid := ?_
    fragmentCoercions := ?_
    fragmentSpecial := ?_
    fragmentRead := ?_
    profile := inventory.contracts }
  · simpa only [atHeader.named] using
      inventory.constructor_law currentContext (CompatibleExpressionBuiltins.Syntax (source fixture.packet.named))
  · intro candidate node tree found
    exact inventory.fragment_coercions (atHeader.named ▸ tree) (atHeader.named ▸ found)
  · intro candidate tree child budget
    have pointwise := inventory.builtin_policy originalRoot currentScope (atHeader.named ▸ tree)
    have special := pointwise.special child budget
    rw [samePolicy] at special
    rw [sameContext, sameSource]
    exact special
  · intro candidate tree
    have pointwise := inventory.builtin_policy originalRoot currentScope (atHeader.named ▸ tree)
    have read := pointwise.read
    rw [samePolicy] at read
    rw [sameSource]
    exact read

variable {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (produced : Produced (compiled := fixture.packet.compiled) caller.named parameters result statements
      sourceContext evidence scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial fixture.packet.compiled.compatible.checked) caller)
      id lowered)
    (inputs : PlaceDiagnosticBodyInputs produced root)

include atHeader selected checked inventory in
/-- The actual literal inputs and constructed globals feed the original bounded
compiler domain once at the fixed indexed read budget. -/
theorem domain_at (currentContext : SourceSemantics.Context) (currentScope : SourceCoreLocalCell.Scope)
    (signatures : currentContext.signatures = fixture.packet.compiled.sourceProgram.signatures) :
    CallableIndexedOwnedPreparedMixedBodyCompilerFactory.DomainAt root.root
      (approved produced root inputs) fixture.packet.compiled.indexed.fuel currentContext evidence currentScope
      (SourceCoreChosenOrdinaryAcceptedCatalogFacts.headers caller) := by
  exact literal_domain produced root inputs
    (globals_at fixture atHeader selected checked inventory root currentContext currentScope signatures)

end Tests.SourceCoreChosenOrdinaryAcceptedLiteralDomainGlobals
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedTyping
/-! Finite checks on the unchanged accepted fixture supply the actual lambda
parameter and return rows. Declarative typing is then constructed from the
original numeric requirement and the genuine lexical extension. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreChosenOrdinaryAcceptedTyping
open Solcore Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open SourceCoreChosenOrdinaryAcceptedFixture
open CallableIndexedNamedGeneration

/-- Each equation refers to an actual retained node or binder. -/
structure Shape (fixture : AcceptedFixture) where
  parameter : TypedBinder
  parameters : fixture.graph.parameters = [parameter]
  owned : parameter.id.owner = (source fixture.packet.named).owner
  scheme : parameter.scheme = .mono parameterType
  requirements : parameter.schemeRequirements = []
  ordinary : parameter.comptime = false
  notInput : (source fixture.packet.named).inputs.any
    (fun input => decide (input.id = parameter.id)) = false
  returnedType : fixture.graph.returned.type = wordType

/-- This check returns proofs of the actual finite shape, without changing
any Source row or using a checker-soundness assumption. -/
def shape (fixture : AcceptedFixture) : Except String (Shape fixture) :=
  match parameters : fixture.graph.parameters with
  | [parameter] =>
    if correct : parameter.id.owner = (source fixture.packet.named).owner ∧
        parameter.scheme = .mono parameterType ∧ parameter.schemeRequirements = [] ∧
        parameter.comptime = false ∧
        (source fixture.packet.named).inputs.any (fun input => decide (input.id = parameter.id)) = false ∧
        fixture.graph.returned.type = wordType then
      .ok ⟨parameter, parameters, correct.1, correct.2.1, correct.2.2.1,
        correct.2.2.2.1, correct.2.2.2.2.1, correct.2.2.2.2.2⟩
    else .error "actual lambda parameter or return type differs"
  | _ => .error "actual lambda parameter count differs"

variable {fixture : AcceptedFixture}

def Shape.bodyContext (given : Shape fixture) : SourceSemantics.Context :=
  (runtimeContext fixture.packet).withLocal given.parameter.id
    given.parameter.scheme given.parameter.schemeRequirements

theorem initial_binders : TypeParameterBindersWellFormed (runtimeContext fixture.packet) := by
  constructor
  · exact List.nodup_nil
  · intro parameter member
    cases member

theorem Shape.body_binders (given : Shape fixture) :
    TypeParameterBindersWellFormed given.bodyContext := initial_binders

theorem Shape.fresh (given : Shape fixture) :
    LocalFresh (runtimeContext fixture.packet) given.parameter.id := by
  constructor <;> exact List.not_mem_nil

/-- The actual monomorphic parameter extends the exact fixture context. -/
theorem Shape.parameters_extend (given : Shape fixture) :
    MonoBindersExtend (source fixture.packet.named).owner (runtimeContext fixture.packet)
      fixture.graph.parameters [parameterType] given.bodyContext := by
  rw [given.parameters]
  refine .cons given.scheme (.intro ?_ given.fresh) (.nil _)
  refine ⟨given.owned, ?_, ?_, fun _ => given.requirements⟩
  · rw [given.scheme]
    exact ⟨initial_binders, List.nodup_nil, .product (.builtin .word) (.builtin .word)⟩
  · rw [given.scheme]
    intro metavariable member
    cases member

/-- Requirement zero is the original solved numeric row in the same body
context; extending a lexical binder does not replace the ledger. -/
theorem Shape.literal_valid (given : Shape fixture) :
    IntegerLiteralValid given.bodyContext (.decimal "7") literalResolution := by
  refine .word (numericLiteralValue?_sound rfl) rfl ?_
  apply numeric_requirement (context := given.bodyContext)
  · exact fixture.runtime.rows
  · exact Or.inl rfl

/-- The genuine literal occurrence is typed with its original requirement. -/
theorem literal_typed (given : Shape fixture) :
    ExpressionHasType (source fixture.packet.named) given.bodyContext
      (expressionId fixture.packet 3) wordType := by
  have valid : TypeAdmissible given.bodyContext wordType := .word given.body_binders
  have typed : ExpressionHasType (source fixture.packet.named) given.bodyContext
      (expressionId fixture.packet 3) fixture.graph.literal.type := by
    refine ExpressionHasType.intro (plan := .ordinary [⟨0⟩]) (lookupExpression?_sound fixture.graph.literalFound) ?_ ?_ valid ?_ ?_
    · rw [fixture.graph.literalForm]
      exact .integerLiteral given.literal_valid
    · simp only [ExpressionNode.rawType, fixture.graph.literalCoercions, fixture.graph.literalType]
    · simpa only [fixture.graph.literalType] using valid
    · apply ExpressionRequirementPlan.Valid.ordinary
      · intro id member
        have same : id = ⟨0⟩ := List.mem_singleton.mp member
        subst id
        exact ⟨_, numeric_requirement fixture.runtime.rows (Or.inl rfl)⟩
      · rw [fixture.graph.literalType, fixture.graph.literalCoercions]
        exact .nil _
      · simp only [fixture.graph.literalRequirements, fixture.graph.literalCoercions]
        rfl
  simpa only [fixture.graph.literalType] using typed

def returnFacts : StatementFacts := {
  type := wordType, hasValue := true, sawReturn := true, control := .returned }

/-- The real return row uses the literal derivation at the installed body
context and the checked return node type. -/
theorem return_typed (given : Shape fixture) :
    StatementHasType (source fixture.packet.named) ⟨wordType, 0⟩ given.bodyContext
      (statementId fixture.packet 2) given.bodyContext returnFacts :=
  .returnValue (lookupStatement?_sound fixture.graph.returnedFound)
    fixture.graph.returnedForm (literal_typed given) given.returnedType

theorem body_typed (given : Shape fixture) :
    StatementsHaveType (source fixture.packet.named) ⟨wordType, 0⟩ given.bodyContext
      [statementId fixture.packet 2] given.bodyContext (BodyFacts.singleton returnFacts) :=
  .singleton (return_typed given)

theorem body_completes : BodyCompletes wordType (BodyFacts.singleton returnFacts) := by
  exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩

/-- The actual lambda judgment is built from its genuine binder extension
and singleton return, at the original runtime context. -/
theorem lambda_typed (given : Shape fixture) :
    ExpressionHasType (source fixture.packet.named) (runtimeContext fixture.packet)
      (expressionId fixture.packet 1) fixture.graph.lambdaNode.type := by
  have word : TypeAdmissible (runtimeContext fixture.packet) wordType := .word initial_binders
  have function : TypeAdmissible (runtimeContext fixture.packet) (.function parameterType wordType) :=
    .function (.product word word) word
  refine ExpressionHasType.intro (plan := .ordinary []) (lookupExpression?_sound fixture.graph.lambdaFound) ?_ ?_ function ?_ ?_
  · rw [fixture.graph.lambdaForm]
    apply ExpressionFormHasRawType.lambda (parameterTypes := [parameterType])
    · rw [given.parameters]
      simp
    · exact given.parameters_extend
    · exact body_typed given
    · exact body_completes
  · simp only [ExpressionNode.rawType, fixture.graph.lambdaCoercions, fixture.graph.lambdaType]
  · simpa only [fixture.graph.lambdaType] using function
  · apply ExpressionRequirementPlan.Valid.ordinary
    · intro id member
      cases member
    · rw [fixture.graph.lambdaType, fixture.graph.lambdaCoercions]
      exact .nil _
    · simp only [fixture.graph.lambdaRequirements, fixture.graph.lambdaCoercions]
      rfl

/-- Raw lambda facts come from this actual typing judgment and the original
well-formed occurrence graph, independently of native compiler typing. -/
theorem source_facts (given : Shape fixture) :
    CallableIndexedOwnedOrdinaryLambdaSourceFacts.Facts
      (CallableIndexedLambdaGeneration.closure fixture.packet.named fixture.graph.parameters
        wordType [statementId fixture.packet 2] (runtimeContext fixture.packet) [] [])
      (expressionId fixture.packet 1) fixture.graph.lambdaNode := by
  exact CallableIndexedOwnedOrdinaryLambdaSourceFacts.of_typed
    fixture.runtime.source_runtime.graph.nodeOccurrencesUnique fixture.graph.lambdaFound
    fixture.graph.lambdaForm (lambda_typed given) fixture.graph.lambdaCoercions

/-- Execute the finite receipt check over the unchanged compiler fixture.
The declarative judgments above remain kernel proofs of those exact rows. -/
def run : IO Unit := do
  match acceptedFixture with
  | .error error => throw (IO.userError error)
  | .ok fixture =>
    match shape fixture with
    | .error error => throw (IO.userError error)
    | .ok _ => IO.println "accepted lambda Source typing: actual monomorphic parameter and Word return checked"

end Tests.SourceCoreChosenOrdinaryAcceptedTyping
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedLiteralInputs
/-! The accepted fixture supplies the literal shell's actual Source fields.
All compiler identities belong to the same selected Produced and root. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreChosenOrdinaryAcceptedLiteralInputs
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
open CallableIndexedOwnedContextualLambdaSourceDiagnostics
open CallableIndexedOwnedLiteralReturnSiteShells
open CallableIndexedOwnedLiteralPlaceDiagnosticShells

variable (fixture : AcceptedFixture) {caller : ActualHeader fixture}
    (atHeader : HeaderAt fixture caller)
    (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
    (metadata : SourceCoreChosenOrdinaryAcceptedBodyMetadata.Receipt fixture.packet fixture.graph)
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation fixture.packet.compiled.indexed caller.named diagnostics namedCode}
    {rootFuel : Nat} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
    (root : LiteralRootReceipt (compiled := fixture.packet.compiled) caller.named diagnostics namedCode compilation
      rootFuel (source fixture.packet.named) (initialScope fixture.packet)
      (expressionId fixture.packet 1) rootReasonAt rootLowered)
    {lowered : SourceCoreBasic.LoweredExpr}
    (produced : Produced (compiled := fixture.packet.compiled) caller.named fixture.graph.parameters wordType
      [statementId fixture.packet 2] (runtimeContext fixture.packet) [] (initialScope fixture.packet)
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial fixture.packet.compiled.compatible.checked) caller)
      (expressionId fixture.packet 1) lowered)

include atHeader in
/-- The selected Code's original Source lookup identifies the retained lambda row. -/
theorem source_node : produced.site.code.sourceNode = fixture.graph.lambdaNode := by
  have found : (source fixture.packet.named).lookupExpression? (expressionId fixture.packet 1) =
      some produced.site.code.sourceNode := by
    simpa only [closure, produced.identifier, atHeader.named] using produced.site.code.sourceFound
  exact Option.some.inj (found.symm.trans fixture.graph.lambdaFound)

/-- The fixture's independent context retains the real catalog signatures. -/
theorem signatures : (runtimeContext fixture.packet).signatures =
    fixture.packet.compiled.compatible.checked.signatures := by
  have owned := fixture.packet.compiled.indexed.base.signatureOwnership
  rw [(SourceCoreUnifiedPreparationCertificates.compiled_fields fixture.packet.compiled).1] at owned
  exact owned.symm

/-- The original declaration context has no assumptions to populate with evidence. -/
theorem covers : Dynamic.EvidenceEnvironment.Covers (runtimeContext fixture.packet) [] := by
  constructor
  · intro goal evidence found
    cases found
  · intro predicate member
    cases member

include atHeader shape metadata in
/-- Every Source and body field is constructed from the actual fixture.
Issued diagnostic preparation and policy/view identity remain genuine compiler receipts. -/
theorem body_inputs
    (issued : IssuedSource fixture.packet.compiled produced.site.code.compilation.owner (source caller.named))
    (sameAssignments : issued.assignments = produced.compilation.own.assignments)
    (samePlaces : PlaceReasonsEq issued.diagnostics.program produced.diagnostics)
    (samePolicy : produced.site.code.policy = root.root.selected.policy)
    (sameView : produced.site.code.view = source caller.named)
    (bodyReasons : CallableIndexedOwnedContextualLambdaProvenance.BodyReasons produced.site.code caller.named) :
    Nonempty (PlaceDiagnosticBodyInputs produced root) := by
  have sameNode := source_node fixture atHeader produced
  refine ⟨{
    issued := issued
    sameAssignments := sameAssignments
    placeReasons := samePlaces
    samePolicy := samePolicy
    canonical := sameView
    bodyReasons := bodyReasons
    typed := ?_
    lambdaCoercions := ?_
    signatures := signatures fixture
    runtime := ?_
    covers := covers fixture
    kinds := ?_
    declarations := ?_
    ledger := ?_
    statement := statementId fixture.packet 2
    statementNode := fixture.graph.returned
    expression := expressionId fixture.packet 3
    expressionNode := fixture.graph.literal
    singleton := rfl
    statementFound := ?_
    statementForm := fixture.graph.returnedForm
    statementOwner := ?_
    statementCore := .word
    statementProjected := metadata.projected
    expressionFound := ?_
    atomic := ?_
    unitType := ?_
    owned := [⟨0⟩]
    ordinaryRequirements := fixture.graph.literalOwned
    literalCoercions := fixture.graph.literalCoercions
    literalRequirements := Or.inr ⟨_, _, fixture.graph.literalForm⟩
    initializer := ?_
    noMatches := ?_ }⟩
  · rw [sameNode, atHeader.named]
    exact SourceCoreChosenOrdinaryAcceptedTyping.lambda_typed shape
  · rw [sameNode]
    exact fixture.graph.lambdaCoercions
  · rw [atHeader.named]
    exact fixture.runtime.source_runtime
  · intro binder member
    rw [shape.parameters] at member
    have same := List.mem_singleton.mp member
    subst binder
    simpa only [atHeader.named] using shape.notInput
  · simpa only [atHeader.named] using metadata.initial_declarations
  · rw [atHeader.named]
    rfl
  · simpa only [atHeader.named] using fixture.graph.returnedFound
  · rw [atHeader.named]
    rfl
  · simpa only [atHeader.named] using fixture.graph.literalFound
  · rw [fixture.graph.literalForm]
    exact .integer _ _
  · rw [fixture.graph.literalForm]
    intro impossible
    cases impossible
  · simpa only [atHeader.named, context, CompatibleNamedBody.bodyContext] using fixture.calls.literalOrdinary
  · simpa only [atHeader.named] using metadata.no_matches

include atHeader shape metadata in
/-- The actual static body shell follows from these constructed Source fields. -/
theorem shell
    (issued : IssuedSource fixture.packet.compiled produced.site.code.compilation.owner (source caller.named))
    (sameAssignments : issued.assignments = produced.compilation.own.assignments)
    (samePlaces : PlaceReasonsEq issued.diagnostics.program produced.diagnostics)
    (samePolicy : produced.site.code.policy = root.root.selected.policy)
    (sameView : produced.site.code.view = source caller.named)
    (bodyReasons : CallableIndexedOwnedContextualLambdaProvenance.BodyReasons produced.site.code caller.named)
    (readFuel : Nat) :
    ∃ inputs : PlaceDiagnosticBodyInputs produced root,
      Nonempty (CallableIndexedOwnedPreparedMixedBodyCompilerFactory.SiteShell
        (approved produced root inputs) produced) := by
  obtain ⟨inputs⟩ := body_inputs fixture atHeader shape metadata root produced issued sameAssignments samePlaces samePolicy sameView bodyReasons
  exact ⟨inputs, literal_shell produced root inputs readFuel⟩

end Tests.SourceCoreChosenOrdinaryAcceptedLiteralInputs
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedIssuedShell
/-! The actual fixture supplies its original diagnostic issuer at the chosen
Produced. Its inventory closes diagnostic typing before the literal shell is built. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreChosenOrdinaryAcceptedIssuedShell
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
open CallableIndexedOwnedContextualLambdaSourceDiagnostics
open CallableIndexedOwnedLiteralReturnSiteShells
open CallableIndexedOwnedLiteralPlaceDiagnosticShells

variable (fixture : AcceptedFixture) {caller : ActualHeader fixture}
    (atHeader : HeaderAt fixture caller)
    (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
    (metadata : SourceCoreChosenOrdinaryAcceptedBodyMetadata.Receipt fixture.packet fixture.graph)
    (inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory fixture)
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation fixture.packet.compiled.indexed caller.named diagnostics namedCode}
    {rootFuel : Nat} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
    (root : LiteralRootReceipt (compiled := fixture.packet.compiled) caller.named diagnostics namedCode compilation
      rootFuel (source fixture.packet.named) (initialScope fixture.packet)
      (expressionId fixture.packet 1) rootReasonAt rootLowered)
    {lowered : SourceCoreBasic.LoweredExpr}
    (produced : Produced (compiled := fixture.packet.compiled) caller.named fixture.graph.parameters wordType
      [statementId fixture.packet 2] (runtimeContext fixture.packet) [] (initialScope fixture.packet)
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial fixture.packet.compiled.compatible.checked) caller)
      (expressionId fixture.packet 1) lowered)

include atHeader inventory in
/-- The unchanged node inventory supplies diagnostic typing at the actual Header. -/
theorem diagnostic_typing :
    EmittedDiagnosticTokenPlan.UnaryTyped (source caller.named) ∧
      AssignmentDiagnosticOrigins.OperandsTyped (source caller.named) := by
  simpa only [atHeader.named] using inventory.typing

include atHeader inventory in
/-- Original preparation and the selected compilation issue the same assignments.
The optional callable root table changes only the effective diagnostic table. -/
theorem issued_at_produced
    (diagnosticsEq : produced.diagnostics =
      effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) :
    ∃ issued : IssuedSource fixture.packet.compiled produced.site.code.compilation.owner (source caller.named),
      issued.assignments = produced.compilation.own.assignments ∧
      PlaceReasonsEq issued.diagnostics.program produced.diagnostics := by
  exact CallableIndexedOwnedLiteralIssuedSourceReceipts.at_produced caller produced
    fixture.packet.diagnosticsFound diagnosticsEq (diagnostic_typing fixture atHeader inventory)

include atHeader inventory in
/-- The original callback identities retain the same assignment row and places.
No new compilation or contextual selection is performed. -/
theorem issued_at_callback
    {callbackCode : Expr}
    (callback : Compilation fixture.packet.compiled.indexed caller.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) callbackCode)
    (diagnosticsEq : produced.diagnostics =
      effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics)
    (codeEq : produced.namedCode = callbackCode)
    (compilationEq : HEq produced.compilation callback) :
    ∃ issued : IssuedSource fixture.packet.compiled produced.site.code.compilation.owner (source caller.named),
      issued.assignments = callback.own.assignments ∧
      PlaceReasonsEq issued.diagnostics.program
        (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) := by
  exact CallableIndexedOwnedLiteralIssuedSourceReceipts.at_callback caller produced callback
    diagnosticsEq codeEq compilationEq fixture.packet.diagnosticsFound rfl
    (diagnostic_typing fixture atHeader inventory)

include atHeader shape metadata inventory in
/-- The real issuer and Source facts populate the chosen Produced's literal inputs. -/
theorem body_inputs
    (diagnosticsEq : produced.diagnostics =
      effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics)
    (samePolicy : produced.site.code.policy = root.root.selected.policy)
    (sameView : produced.site.code.view = source caller.named)
    (bodyReasons : CallableIndexedOwnedContextualLambdaProvenance.BodyReasons produced.site.code caller.named) :
    Nonempty (PlaceDiagnosticBodyInputs produced root) := by
  obtain ⟨issued, assignments, places⟩ :=
    issued_at_produced fixture atHeader inventory produced diagnosticsEq
  exact SourceCoreChosenOrdinaryAcceptedLiteralInputs.body_inputs
    fixture atHeader shape metadata root produced issued assignments places samePolicy sameView bodyReasons

include atHeader shape metadata inventory in
/-- One original issuer and the actual static inputs construct the same body's shell. -/
theorem shell
    (diagnosticsEq : produced.diagnostics =
      effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics)
    (samePolicy : produced.site.code.policy = root.root.selected.policy)
    (sameView : produced.site.code.view = source caller.named)
    (bodyReasons : CallableIndexedOwnedContextualLambdaProvenance.BodyReasons produced.site.code caller.named)
    (readFuel : Nat) :
    ∃ inputs : PlaceDiagnosticBodyInputs produced root,
      Nonempty (CallableIndexedOwnedPreparedMixedBodyCompilerFactory.SiteShell
        (approved produced root inputs) produced) := by
  obtain ⟨inputs⟩ := body_inputs fixture atHeader shape metadata inventory root produced
    diagnosticsEq samePolicy sameView bodyReasons
  exact ⟨inputs, literal_shell produced root inputs readFuel⟩

end Tests.SourceCoreChosenOrdinaryAcceptedIssuedShell
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedNativeTyping
/-! The actual initializer is typed before any Produced or Site is selected.
Its accepted lambda certificate retains the original parameter compiler,
literal body callback, allocation, snapshot and callable descriptor. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreChosenOrdinaryAcceptedNativeTyping
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open CallableIndexedNamedGeneration CallableIndexedLambdaCertificates
open CallableIndexedParameterNativeTyping CallableIndexedLambdaScalarNativeTyping
open CallableIndexedOwnedLiteralReturnSiteShells

variable (fixture : AcceptedFixture) {caller : ActualHeader fixture}
    (atHeader : HeaderAt fixture caller)
    (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
    (metadata : SourceCoreChosenOrdinaryAcceptedBodyMetadata.Receipt fixture.packet fixture.graph)
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation fixture.packet.compiled.indexed caller.named diagnostics namedCode}
    {fuel : Nat} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (root : LiteralRootReceipt (compiled := fixture.packet.compiled) caller.named diagnostics namedCode compilation
      fuel (source fixture.packet.named) (initialScope fixture.packet) (expressionId fixture.packet 1) reasonAt lowered)

/-- This is the original body recipe at its retained recursive callback. -/
def loopPolicy : SourceCoreLoops.Policy :=
  let actual := (representation fixture.packet.compiled.indexed).atContext caller.named.signature.key []
  {actual.loopsWithSourceCells actual.expressions.sourceCells
    (context fixture.packet.compiled.indexed caller.named).solvedRequirements compilation.own.assignments diagnostics
    (context fixture.packet.compiled.indexed caller.named).owner
    (FunctionCode.children root.root.selected.policy root.root.selected.lowerBody fuel
      (context fixture.packet.compiled.indexed caller.named)) with
    sourceCells := actual.expressions.sourceCells
    lowerBinder := SourceCoreGeneralFunctions.contextualBinder actual
      fixture.packet.compiled.indexed.base.locals caller.named.signature.key []}

theorem body_callback :
    root.root.selected.lowerBody
      (FunctionCode.children root.root.selected.policy root.root.selected.lowerBody fuel
        (context fixture.packet.compiled.indexed caller.named)) =
      SourceCoreLoops.lowerStatementsWithPolicy (loopPolicy fixture root) := by
  dsimp only [loopPolicy]
  rw [root.root.selected.recipe]
  rfl

private theorem descriptor_exists (table : SourceCoreStageCodebook.Table)
    {origin : SourceCoreStageCodebook.Origin} {id : Word}
    (selected : table.idAt? origin = some id) :
    Nonempty (SourceCoreCallableContracts.Descriptor table origin) := by
  cases accepted : SourceCoreCallableContracts.descriptor table origin with
  | error error =>
    unfold SourceCoreCallableContracts.descriptor at accepted
    split at accepted
    · rename_i absent
      rw [selected] at absent
      cases absent
    · cases accepted
  | ok actual => exact ⟨actual⟩

private theorem singleton_bindings (bindings : List CallableIndexedParameterCertificates.Binding)
    (parameter : TypedBinder) (same : bindings.map Prod.fst = [parameter]) :
    ∃ type, bindings = [(parameter, type)] := by
  cases bindings with
  | nil => cases same
  | cons head tail =>
    cases tail with
    | nil =>
      have first := (List.cons.inj same).1
      exact ⟨head.2, congrArg (fun binding => [binding]) (Prod.ext first rfl)⟩
    | cons next rest =>
      have impossible := (List.cons.inj same).2
      cases impossible

private theorem final_frame (parameter frame : Ty) (globals : Core.Context) :
    (parameter :: globals ++ [.cell frame])[1 + globals.length]? = some (.cell frame) := by
  rw [Nat.add_comm 1, List.cons_append, List.getElem?_cons_succ]
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp only [Nat.sub_self, List.getElem?_cons_zero]

include shape in
/-- The real singleton parameter compiler fixes its exact native bundle. -/
theorem parameter_bundle {reported : Ty}
    (certificate : Certificate root.root.selected.policy root.root.selected.lowerBody fuel
      (context fixture.packet.compiled.indexed caller.named) (source fixture.packet.named)
      (initialScope fixture.packet) (expressionId fixture.packet 1) fixture.graph.lambdaNode
      fixture.graph.parameters wordType [statementId fixture.packet 2] reported reasonAt lowered) :
    certificate.parameterCore = packed (certificate.loweredParameters.map Prod.snd) := by
  have monomorphic : ∀ binder ∈ fixture.graph.parameters, binder.scheme.quantified = [] := by
    intro binder member
    rw [shape.parameters] at member
    have same := List.mem_singleton.mp member
    subst binder
    rw [shape.scheme]
    rfl
  have projections := parameter_projections certificate.parametersCompiled root.root.selected.binder
    (by rfl) monomorphic
  have binders := (FunctionCode.Parameters.of_accepted certificate.parametersCompiled).binders
  have binders : certificate.loweredParameters.map Prod.fst = [shape.parameter] := binders.trans shape.parameters
  obtain ⟨type, bindings⟩ := singleton_bindings _ _ binders
  have sameParameter : TypeSystem.Ty.productMany ([shape.parameter].map (·.scheme.body)) = certificate.parameter :=
    (congrArg (fun parameters : List TypedBinder => TypeSystem.Ty.productMany (parameters.map (·.scheme.body))) shape.parameters).symm.trans certificate.parameterTypes
  change shape.parameter.scheme.body = certificate.parameter at sameParameter
  have parameterProjected := CompatibleExpressionReads.projectType_of_accepted
    (root.root.projectType ▸ certificate.parameterProjected)
  have bindingProjected := CompatibleExpressionReads.projectType_of_accepted
    (projections (shape.parameter, type) (by rw [bindings]; exact List.mem_singleton_self _))
  rw [← sameParameter] at parameterProjected
  have same := Except.ok.inj (parameterProjected.symm.trans bindingProjected)
  simpa only [bindings, List.map_cons, List.map_nil, packed] using same

include atHeader shape metadata root in
/-- Native typing follows from the same accepted root and its literal body.
No Site, Produced, body meaning or native typing field is an input. -/
theorem native_at_root :
    HasType (SourceCoreLocalCell.coreContext (initialScope fixture.packet) ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial fixture.packet.compiled.compatible.checked) caller)
      lowered.expression (LanguageResult.resultType lowered.type) fixture.packet.compiled.indexed.layouts.definitions := by
  have found : (source caller.named).lookupExpression? (expressionId fixture.packet 1) = some fixture.graph.lambdaNode := by
    simpa only [atHeader.named] using fixture.graph.lambdaFound
  have ordinary : fixture.packet.compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context fixture.packet.compiled.indexed caller.named).owner ∧
        binding.initializer = expressionId fixture.packet 1)) = none := by
    simpa only [atHeader.named, context, CompatibleNamedBody.bodyContext] using fixture.calls.lambdaOrdinary
  have pointwise := CallableIndexedOwnedContextualCompilerPolicyProfiles.lambda_policy root.root
    (scope := initialScope fixture.packet) (reasonAt := reasonAt) fixture.graph.lambdaFound fixture.graph.lambdaForm
    fixture.graph.lambdaRequirements fixture.graph.lambdaCoercions ordinary
  have sourceEq : source caller.named = source fixture.packet.named := congrArg source atHeader.named
  have callerPointwise : CallableIndexedOwnedContextualCompilerPolicyProfiles.PointwiseFor root.root
      (source caller.named) (initialScope fixture.packet) (expressionId fixture.packet 1) reasonAt :=
    sourceEq.symm ▸ pointwise
  have accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.root.selected.policy root.root.selected.lowerBody
      (fuel + 1) (context fixture.packet.compiled.indexed caller.named) (source caller.named)
      (initialScope fixture.packet) (expressionId fixture.packet 1) reasonAt = .ok lowered := by
    exact sourceEq.symm ▸ root.root.selected.accepted
  obtain ⟨reported, read⟩ := CallableIndexedOwnedPreparedMixedBodySiteInputs.lambda_read root.root
    found fixture.graph.lambdaForm callerPointwise accepted
  have canonicalRead : SourceCoreCompatibleDataExpressions.readExpression fixture.packet.compiled.compatible.checked
      (source fixture.packet.named) (expressionId fixture.packet 1) = .ok (fixture.graph.lambdaNode, reported) :=
    sourceEq ▸ read
  have actualRead : root.root.selected.policy.readExpression (source fixture.packet.named)
      (expressionId fixture.packet 1) = .ok (fixture.graph.lambdaNode, reported) := by
    exact pointwise.read.trans canonicalRead
  have readMetadata := CompatibleExpressionReads.metadata_of_read canonicalRead
  obtain ⟨certificate⟩ := CallableIndexedLambdaCertificates.of_accepted
    (show DecoratedFunctionCode.SpecialPasses root.root.selected.policy root.root.selected.lowerBody fuel
      (context fixture.packet.compiled.indexed caller.named) (source fixture.packet.named)
      (initialScope fixture.packet) (expressionId fixture.packet 1) reasonAt from by
        exact pointwise.special _ _)
    readMetadata.owner fixture.graph.lambdaFound actualRead
    fixture.graph.lambdaForm root.root.selected.accepted
  have bodyAccepted := certificate.bodyCompiled
  rw [body_callback fixture root] at bodyAccepted
  have returnRead : (loopPolicy fixture root).readStatement (source fixture.packet.named)
      (statementId fixture.packet 2) = .ok (fixture.graph.returned, .word) := metadata.return_read
  have literalPolicy := literal_policy root.root (childSource := source fixture.packet.named)
    (childScope := certificate.bodyScope) (reasonAt := reasonAt) fixture.graph.literalFound
    (by rw [fixture.graph.literalForm]; exact .integer _ _) fixture.graph.literalOwned
    fixture.graph.literalCoercions (.inr ⟨_, _, fixture.graph.literalForm⟩)
    (by simpa only [atHeader.named, context, CompatibleNamedBody.bodyContext] using fixture.calls.literalOrdinary)
  have bodyTyped := CallableIndexedOwnedLiteralReturnLambdaStaticFacts.literal_body_native
    (show (loopPolicy fixture root).lowerExpression = FunctionCode.children root.root.selected.policy
      root.root.selected.lowerBody fuel (context fixture.packet.compiled.indexed caller.named) from rfl)
    returnRead fixture.graph.returnedForm bodyAccepted fixture.graph.literalFound
    (by rw [fixture.graph.literalForm]; exact .integer _ _)
    (by rw [fixture.graph.literalForm]; intro impossible; cases impossible)
    literalPolicy.special literalPolicy.read root.leaf fixture.packet.compiled.indexed.layouts.definitions
    (SourceCoreLocalCell.coreContext certificate.bodyScope ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial fixture.packet.compiled.compatible.checked) caller)
  have monomorphic : ∀ binder ∈ fixture.graph.parameters, binder.scheme.quantified = [] := by
    intro binder member
    rw [shape.parameters] at member
    have same := List.mem_singleton.mp member
    subst binder
    rw [shape.scheme]
    rfl
  have projections := parameter_projections certificate.parametersCompiled root.root.selected.binder (by rfl) monomorphic
  have parameterWF := fun binding member => CompatibleExpressionReads.projectType_wellFormed (projections binding member)
  have ordinaryBindings : ∀ binding ∈ certificate.loweredParameters,
      (source fixture.packet.named).inputs.any (fun input => decide (input.id = binding.1.id)) = false := by
    intro binding member
    have belongs : binding.1 ∈ fixture.graph.parameters := by
      rw [← (FunctionCode.Parameters.of_accepted certificate.parametersCompiled).binders]
      exact List.mem_map.mpr ⟨binding, member, rfl⟩
    rw [shape.parameters] at belongs
    simpa only [List.mem_singleton.mp belongs] using shape.notInput
  have emptyScope : initialScope fixture.packet = [] := by simp only [initialScope, metadata.inputs, List.reverse_nil, List.map_nil]
  have scopeWF : ∀ binding : Resolved.LocalId × Ty, binding ∈ initialScope fixture.packet →
      binding.2.WellFormed fixture.packet.compiled.compatible.checked.catalog.definitions := by
    simp only [emptyScope, List.not_mem_nil, false_implies, implies_true]
  have current : (SourceCoreLocalCell.coreContext (initialScope fixture.packet) ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial fixture.packet.compiled.compatible.checked) caller)[
        (initialScope fixture.packet).length + 1 + fixture.packet.compiled.indexed.base.globals.length]? =
      some (.cell fixture.packet.compiled.indexed.ancestry.layout.frame.type) := by
    simpa only [emptyScope, SourceCoreLocalCell.coreContext, List.map_nil, List.nil_append,
      List.length_nil, Nat.zero_add, RecursiveNamedLambdaFormationHeads.nativePrefix, List.length_map] using
      final_frame caller.named.signature.parameterType fixture.packet.compiled.indexed.ancestry.layout.frame.type
        (fixture.packet.compiled.indexed.base.globals.map (·.referenceType))
  have hook := certificate.expressionHook
  rw [root.root.rawLambdaExpression] at hook
  obtain ⟨origin, _, selected, _, _, _, _, _⟩ :=
    CallableIndexedFormation.expressionHook_receipt fixture.packet.compiled.indexed.ancestry hook
  rw [(lookupExpression?_sound fixture.graph.lambdaFound).2] at selected
  obtain ⟨descriptor⟩ := descriptor_exists _ selected
  exact certificate_native fixture.packet.compiled.indexed certificate root.root.projectType root.root.sourceCells
    root.root.rawLambdaBody root.root.rawLambdaExpression root.root.callables descriptor rfl
    (parameter_bundle fixture shape root certificate) parameterWF ordinaryBindings scopeWF
    (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial fixture.packet.compiled.compatible.checked) caller)
    current bodyTyped

include atHeader shape metadata in
/-- The original initializer selector supplies this typing before the factory
receives its accepted lambda action. The parent callback remains independent. -/
theorem initializer_native
    (compilation : Compilation fixture.packet.compiled.indexed fixture.packet.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode) :
    HasType (SourceCoreLocalCell.coreContext (initialScope fixture.packet) ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial fixture.packet.compiled.compatible.checked) caller)
      fixture.calls.initializer.expression (LanguageResult.resultType fixture.calls.initializer.type)
      fixture.packet.compiled.indexed.layouts.definitions := by
  let original := fixture.calls.initializer_root compilation
  have actualRoot := Eq.rec
    (motive := fun (named : Named) (same : fixture.packet.named = named) =>
      LiteralRootReceipt (compiled := fixture.packet.compiled) named
        (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode
        (same ▸ compilation) 498 (source fixture.packet.named) (initialScope fixture.packet)
        (expressionId fixture.packet 1)
        ((effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key)
        fixture.calls.initializer)
    original atHeader.named.symm
  exact native_at_root fixture atHeader shape metadata actualRoot

end Tests.SourceCoreChosenOrdinaryAcceptedNativeTyping
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedOuterTyping
/-! The original accepted fixture's outer let and indirect call receive a
finite declarative Source typing proof. All retained binder and node types
come from checks over the unchanged fixture; native typing is independent. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreChosenOrdinaryAcceptedOuterTyping
open Solcore Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open SourceCoreChosenOrdinaryAcceptedFixture CallableIndexedNamedGeneration

def functionType : TypeSystem.Ty := .function parameterType wordType

/-- These are actual retained fields missing from the earlier lookup receipt. -/
structure Metadata (fixture : AcceptedFixture) : Prop where
  owned : fixture.graph.binder.id.owner = (source fixture.packet.named).owner
  scheme : fixture.graph.binder.scheme = .mono functionType
  requirements : fixture.graph.binder.schemeRequirements = []
  ordinary : fixture.graph.binder.comptime = false
  initializedType : fixture.graph.initialized.type = .unit
  leftType : fixture.parentRows.left.type = wordType
  rightType : fixture.parentRows.right.type = wordType
  calleeType : fixture.graph.callee.type = functionType
  argumentType : fixture.graph.argument.type = parameterType
  returnedType : fixture.graph.outerReturn.type = wordType
  resultType : fixture.packet.named.specialized.function.inferredBodyType = wordType

/-- The finite checker returns the equations of the original fields. -/
def metadata (fixture : AcceptedFixture) : Except String (PLift (Metadata fixture)) :=
  if correct : fixture.graph.binder.id.owner = (source fixture.packet.named).owner ∧
      fixture.graph.binder.scheme = .mono functionType ∧ fixture.graph.binder.schemeRequirements = [] ∧
      fixture.graph.binder.comptime = false ∧ fixture.graph.initialized.type = .unit ∧
      fixture.parentRows.left.type = wordType ∧ fixture.parentRows.right.type = wordType ∧
      fixture.graph.callee.type = functionType ∧ fixture.graph.argument.type = parameterType ∧
      fixture.graph.outerReturn.type = wordType ∧
      fixture.packet.named.specialized.function.inferredBodyType = wordType then
    let ⟨owned, scheme, requirements, ordinary, initializedType, leftType, rightType,
      calleeType, argumentType, returnedType, resultType⟩ := correct
    .ok ⟨⟨owned, scheme, requirements, ordinary, initializedType, leftType, rightType,
      calleeType, argumentType, returnedType, resultType⟩⟩
  else .error "actual outer binder or occurrence types differ"

variable {fixture : AcceptedFixture}

def localContext (fixture : AcceptedFixture) : SourceSemantics.Context :=
  (runtimeContext fixture.packet).withLocal fixture.graph.binder.id
    fixture.graph.binder.scheme fixture.graph.binder.schemeRequirements

theorem local_binders : TypeParameterBindersWellFormed (localContext fixture) :=
  SourceCoreChosenOrdinaryAcceptedTyping.initial_binders

theorem function_admissible (context : SourceSemantics.Context)
    (binders : TypeParameterBindersWellFormed context) : TypeAdmissible context functionType :=
  .function (.product (.word binders) (.word binders)) (.word binders)

theorem Metadata.binder (given : Metadata fixture) :
    BinderWellFormed (runtimeContext fixture.packet) (source fixture.packet.named).owner fixture.graph.binder := by
  refine ⟨given.owned, ?_, ?_, fun _ => given.requirements⟩
  · rw [given.scheme]
    exact SchemeWellFormed.monoAdmissible (function_admissible _ SourceCoreChosenOrdinaryAcceptedTyping.initial_binders)
  · rw [given.scheme]
    intro metavariable member
    cases member

theorem fresh : LocalFresh (runtimeContext fixture.packet) fixture.graph.binder.id := by
  constructor <;> exact List.not_mem_nil

theorem Metadata.extended (given : Metadata fixture) :
    BinderExtends (source fixture.packet.named).owner (runtimeContext fixture.packet)
      fixture.graph.binder (localContext fixture) := .intro given.binder fresh

theorem Metadata.generalizes (given : Metadata fixture) :
    SchemeGeneralizes (runtimeContext fixture.packet) fixture.graph.binder.scheme := by
  rw [given.scheme]
  rfl

def letFacts : StatementFacts := {
  type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit }

/-- The already proved lambda initializes the real fresh outer binder. -/
theorem initialized_typed (lambda : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
    (given : Metadata fixture) :
    StatementHasType (source fixture.packet.named) ⟨wordType, 0⟩ (runtimeContext fixture.packet)
      (statementId fixture.packet 0) (localContext fixture) letFacts := by
  apply StatementHasType.letInitialized (lookupStatement?_sound fixture.graph.initializedFound)
    fixture.graph.initializedForm
  · simpa only [given.scheme, TypeSystem.Scheme.mono, fixture.graph.lambdaType, functionType] using
      SourceCoreChosenOrdinaryAcceptedTyping.lambda_typed lambda
  · rw [given.scheme]; rfl
  · exact given.generalizes
  · exact given.extended
  · exact given.initializedType

/-- Both paired local tables hold the same genuine binder, instantiated with
one empty substitution and its empty requirement spine. -/
theorem Metadata.reference (given : Metadata fixture) :
    ReferenceUseValid (localContext fixture) (.local fixture.graph.binder.id) functionType [] := by
  refine .local (Context.localLookup_withLocal_self _ _ _ _)
    (Context.localSchemeRequirementsLookup_withLocal_self _ _ _ _) ?_
  refine .intro (LocalSchemeRequirementsWellFormed.empty _ _ given.requirements) ?_ [] ?_ ?_ ?_ List.nodup_nil ?_ ?_
  · rw [given.scheme]
    exact SchemeWellFormed.monoAdmissible (function_admissible _ local_binders)
  · rw [given.scheme]
    exact ExactSubstitution.empty
  · intro metavariable replacement member
    cases member
  · rw [given.scheme]
    exact SchemeInstantiates.empty_apply functionType
  · intro id member
    cases member
  · simp only [instantiateLocalSchemePredicates, given.requirements, List.map_nil]
    exact .nil

theorem callee_typed (given : Metadata fixture) :
    ExpressionHasType (source fixture.packet.named) (localContext fixture)
      (expressionId fixture.packet 9) functionType := by
  have admissible := function_admissible (localContext fixture) local_binders
  have typed : ExpressionHasType (source fixture.packet.named) (localContext fixture)
      (expressionId fixture.packet 9) fixture.graph.callee.type := by
    refine ExpressionHasType.intro (plan := .ordinary []) (lookupExpression?_sound fixture.graph.calleeFound)
      ?_ ?_ admissible ?_ ?_
    · rw [fixture.graph.calleeForm]
      exact .reference given.reference
    · simp only [ExpressionNode.rawType, fixture.parentRows.calleeCoercions, given.calleeType]
    · simpa only [given.calleeType] using admissible
    · apply ExpressionRequirementPlan.Valid.ordinary
      · intro id member; cases member
      · rw [given.calleeType, fixture.parentRows.calleeCoercions]; exact .nil _
      · simp only [fixture.parentRows.calleeRequirements, fixture.parentRows.calleeCoercions]
        rfl
  simpa only [given.calleeType] using typed

private theorem requirements_of_owned {node : ExpressionNode} {requirements : List RequirementId}
    (coercions : node.coercions = [])
    (owned : SourceCompilationPlan.ordinaryOwnedRequirements? node = some requirements) :
    node.requirements = requirements := by
  unfold SourceCompilationPlan.ordinaryOwnedRequirements? at owned
  rw [coercions] at owned
  change (if node.requirements.length < 0 then none else
    if node.requirements = node.requirements.take (node.requirements.length - 0) ++ [] then
      some (node.requirements.take (node.requirements.length - 0)) else none) = some requirements at owned
  simpa using owned

private theorem numeric_typed {packet : Packet} {context : SourceSemantics.Context}
    {id : ExpressionId} {node : ExpressionNode} {literal : Syntax.CoreLiteralValue} {value index : Nat}
    (rows : context.solvedRequirements = numericRows)
    (binders : TypeParameterBindersWellFormed context)
    (found : (source packet.named).lookupExpression? id = some node)
    (form : node.form = .integerLiteral literal (argumentResolution value index))
    (type : node.type = wordType) (coercions : node.coercions = [])
    (owned : SourceCompilationPlan.ordinaryOwnedRequirements? node = some [⟨index⟩])
    (denotes : NumericLiteralDenotes literal value) (member : index = 0 ∨ index = 1 ∨ index = 2) :
    ExpressionHasType (source packet.named) context id wordType := by
  have valid : IntegerLiteralValid context literal (argumentResolution value index) :=
    .word denotes rfl (numeric_requirement rows member)
  have admissible : TypeAdmissible context wordType := .word binders
  have typed : ExpressionHasType (source packet.named) context id node.type := by
    refine ExpressionHasType.intro (plan := .ordinary [⟨index⟩]) (lookupExpression?_sound found) ?_ ?_ admissible ?_ ?_
    · rw [form]; exact .integerLiteral valid
    · simp only [ExpressionNode.rawType, coercions, type]
    · simpa only [type] using admissible
    · apply ExpressionRequirementPlan.Valid.ordinary
      · intro requirement inList
        have same : requirement = ⟨index⟩ := List.mem_singleton.mp inList
        subst requirement
        exact ⟨_, numeric_requirement rows member⟩
      · rw [type, coercions]; exact .nil _
      · rw [requirements_of_owned coercions owned, coercions]
        rfl
  simpa only [type] using typed

theorem left_typed (given : Metadata fixture) :
    ExpressionHasType (source fixture.packet.named) (localContext fixture) (expressionId fixture.packet 7) wordType :=
  numeric_typed fixture.runtime.rows local_binders fixture.parentRows.leftFound fixture.parentRows.leftForm
    given.leftType fixture.parentRows.leftCoercions fixture.parentRows.leftOwned
    (numericLiteralValue?_sound rfl) (Or.inr (Or.inl rfl))

theorem right_typed (given : Metadata fixture) :
    ExpressionHasType (source fixture.packet.named) (localContext fixture) (expressionId fixture.packet 8) wordType :=
  numeric_typed fixture.runtime.rows local_binders fixture.parentRows.rightFound fixture.parentRows.rightForm
    given.rightType fixture.parentRows.rightCoercions fixture.parentRows.rightOwned
    (numericLiteralValue?_sound rfl) (Or.inr (Or.inr rfl))

/-- The one physical argument is the actual pair expression. -/
theorem argument_typed (given : Metadata fixture) :
    ExpressionHasType (source fixture.packet.named) (localContext fixture) (expressionId fixture.packet 6) parameterType := by
  have admissible : TypeAdmissible (localContext fixture) parameterType := .product (.word local_binders) (.word local_binders)
  have typed : ExpressionHasType (source fixture.packet.named) (localContext fixture)
      (expressionId fixture.packet 6) fixture.graph.argument.type := by
    refine ExpressionHasType.intro (plan := .ordinary []) (lookupExpression?_sound fixture.graph.argumentFound)
      ?_ ?_ admissible ?_ ?_
    · rw [fixture.graph.argumentForm]
      exact .tuple (.cons (left_typed given) (.cons (right_typed given) (.nil _)))
    · simp only [ExpressionNode.rawType, fixture.parentRows.argumentCoercions, given.argumentType]
    · simpa only [given.argumentType] using admissible
    · apply ExpressionRequirementPlan.Valid.ordinary
      · intro id member; cases member
      · rw [given.argumentType, fixture.parentRows.argumentCoercions]; exact .nil _
      · simp only [fixture.parentRows.argumentRequirements, fixture.parentRows.argumentCoercions]
        rfl
  simpa only [given.argumentType] using typed

theorem indirect_application : IndirectApplicationValid (localContext fixture) indirectMetadata [parameterType] parameterType :=
  .intro rfl rfl rfl (.nil _)

/-- Callee typing, the physical singleton argument and its actual metadata
construct the raw indirect-call judgment; no Core read is inverted. -/
theorem parent_typed (given : Metadata fixture) :
    ExpressionHasType (source fixture.packet.named) (localContext fixture) (expressionId fixture.packet 5) wordType := by
  have admissible : TypeAdmissible (localContext fixture) wordType := .word local_binders
  have typed : ExpressionHasType (source fixture.packet.named) (localContext fixture)
      (expressionId fixture.packet 5) fixture.graph.parent.type := by
    refine ExpressionHasType.intro (plan := .indirectCall []) (lookupExpression?_sound fixture.graph.parentFound)
      ?_ ?_ admissible ?_ ?_
    · rw [fixture.graph.parentForm]
      exact .indirectCall (callee_typed given) (.cons (argument_typed given) (.nil _)) indirect_application
    · simp only [ExpressionNode.rawType, fixture.graph.parentCoercions, fixture.graph.parentType]
    · simpa only [fixture.graph.parentType] using admissible
    · apply ExpressionRequirementPlan.Valid.indirectCall
      · intro id member; cases member
      · rw [fixture.graph.parentType, fixture.graph.parentCoercions]; exact .nil _
      · simp only [fixture.graph.parentRequirements, fixture.graph.parentCoercions]
        rfl
  simpa only [fixture.graph.parentType] using typed

def returnFacts : StatementFacts := {
  type := wordType, hasValue := true, sawReturn := true, control := .returned }

theorem returned_typed (given : Metadata fixture) :
    StatementHasType (source fixture.packet.named) ⟨wordType, 0⟩ (localContext fixture)
      (statementId fixture.packet 4) (localContext fixture) returnFacts :=
  .returnValue (lookupStatement?_sound fixture.graph.outerReturnFound) fixture.graph.outerReturnForm
    (parent_typed given) given.returnedType

def bodyFacts : BodyFacts := .cons letFacts (.singleton returnFacts)

theorem body_typed (lambda : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture) (given : Metadata fixture) :
    StatementsHaveType (source fixture.packet.named) ⟨wordType, 0⟩ (runtimeContext fixture.packet)
      [statementId fixture.packet 0, statementId fixture.packet 4] (localContext fixture) bodyFacts :=
  .cons (initialized_typed lambda given) (.singleton (returned_typed given))

theorem body_completes : BodyCompletes wordType bodyFacts :=
  ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩

/-- The actual public Header's inferred Source result and body context are
identified by its retained view and the checked original result field. -/
theorem Metadata.header_result (given : Metadata fixture)
    {header : SourceCoreChosenOrdinaryAcceptedHeader.ActualHeader fixture}
    (atHeader : SourceCoreChosenOrdinaryAcceptedHeader.HeaderAt fixture header) :
    header.function.resultType = wordType := by
  have result : header.function.resultType = fixture.packet.named.specialized.function.inferredBodyType := by
    simpa only [atHeader.named] using header.agreement.result
  exact result.trans given.resultType

theorem header_body_typed (lambda : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
    (given : Metadata fixture) {header : SourceCoreChosenOrdinaryAcceptedHeader.ActualHeader fixture}
    (atHeader : SourceCoreChosenOrdinaryAcceptedHeader.HeaderAt fixture header) :
    StatementsHaveType header.function.source ⟨header.function.resultType, 0⟩ header.function.context
      header.function.body (localContext fixture) bodyFacts := by
  rw [atHeader.source, atHeader.functionContext, atHeader.statements, given.header_result atHeader]
  exact body_typed lambda given

theorem header_body_completes (given : Metadata fixture)
    {header : SourceCoreChosenOrdinaryAcceptedHeader.ActualHeader fixture}
    (atHeader : SourceCoreChosenOrdinaryAcceptedHeader.HeaderAt fixture header) :
    BodyCompletes header.function.resultType bodyFacts := by
  rw [given.header_result atHeader]
  exact body_completes

/-- Finite receipt execution is separate from Source/Core runtime equivalence. -/
def run : IO Unit := do
  match acceptedFixture with
  | .error error => throw (IO.userError error)
  | .ok fixture =>
    match SourceCoreChosenOrdinaryAcceptedTyping.shape fixture, metadata fixture with
    | .ok _, .ok _ => IO.println "accepted outer Source typing: actual f binder, argument types and inferred Word result checked"
    | .error error, _ => throw (IO.userError error)
    | _, .error error => throw (IO.userError error)

end Tests.SourceCoreChosenOrdinaryAcceptedOuterTyping
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedArgumentAdmission
/-! The accepted indirect call has one actual pair argument. Its two numeric
children use the retained intrinsic evidence and leave the Source heap intact.
Admission follows these finite Source rules at the actual caller state. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreChosenOrdinaryAcceptedArgumentAdmission
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedOuterTyping
open CallableIndexedNamedGeneration

variable (fixture : AcceptedFixture)

def argumentValue : Dynamic.Value :=
  .product (.word (Word.ofNatModulo 1)) (.word (Word.ofNatModulo 2))

private theorem requirements_of_owned {node : ExpressionNode} {requirements : List RequirementId}
    (coercions : node.coercions = [])
    (owned : SourceCompilationPlan.ordinaryOwnedRequirements? node = some requirements) :
    node.requirements = requirements := by
  unfold SourceCompilationPlan.ordinaryOwnedRequirements? at owned
  rw [coercions] at owned
  change (if node.requirements.length < 0 then none else
    if node.requirements = node.requirements.take (node.requirements.length - 0) ++ [] then
      some (node.requirements.take (node.requirements.length - 0)) else none) = some requirements at owned
  simpa using owned

private theorem numeric_evaluates {context : SourceSemantics.Context} {source : TypedSource}
    {id : ExpressionId} {node : ExpressionNode} {literal : Syntax.CoreLiteralValue}
    {number requirement : Nat} {program : SourceSemantics.Program} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .integerLiteral literal (argumentResolution number requirement))
    (coercions : node.coercions = [])
    (owned : SourceCompilationPlan.ordinaryOwnedRequirements? node = some [⟨requirement⟩])
    (meaning : NumericLiteralDenotes literal number)
    (proves : RequirementProves context ⟨requirement⟩ (ProgramSignatures.builtinIntPredicate wordType)) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap id
      (.word (Word.ofNatModulo number)) heap := by
  refine .intro (raw := .word (Word.ofNatModulo number)) (middle := heap) (lookupExpression?_sound found) ?_ ?_
  · rw [form]
    refine .integerLiteral ?_ (.word meaning proves)
    simp [Dynamic.OrdinaryRequirementLayout, argumentResolution, coercions,
      requirements_of_owned coercions owned, coercionRequirementIds]
  · rw [coercions]
    exact .nil

private theorem numeric_outcome {context : SourceSemantics.Context} {source : TypedSource}
    {id : ExpressionId} {node : ExpressionNode} {literal : Syntax.CoreLiteralValue}
    {number requirement : Nat} {program : SourceSemantics.Program} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (found : source.lookupExpression? id = some node) (unique : NodeOccurrencesUnique source)
    (form : node.form = .integerLiteral literal (argumentResolution number requirement))
    (coercions : node.coercions = [])
    (meaning : NumericLiteralDenotes literal number)
    (proves : RequirementProves context ⟨requirement⟩ (ProgramSignatures.builtinIntPredicate wordType))
    (safe : ¬ Dynamic.RequirementUnavailable context evidence ⟨requirement⟩)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after) :
    outcome = .value (.word (Word.ofNatModulo number)) ∧ after = before := by
  have sameNode : ∀ other, ContainsExpression source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  have nonlocal : ∀ name binder, node.form ≠ .reference name (.local binder) := by
    intros
    rw [form]
    simp
  cases trace with
  | value evaluated =>
    cases evaluated with
    | intro other raw path =>
      have same := sameNode _ other
      subst same
      rw [coercions] at path
      cases path
      rw [form] at raw
      cases raw with
      | integerLiteral _ constructed =>
        have expected : Dynamic.ResolvedIntegerLiteralConstructs context literal
            (argumentResolution number requirement) (.word (Word.ofNatModulo number)) := .word meaning proves
        exact ⟨congrArg _ (constructed.functional expected), rfl⟩
    | generalizedLocal contains otherForm _ _ _ _ _ _ _ =>
      exact False.elim (nonlocal _ _ (sameNode _ contains ▸ otherForm))
  | @fault _ _ reason failed =>
    have rawFault : Dynamic.ExpressionFormFaults program context evidence source environment before
        node.form node.requirements node.coercions reason after := by
      cases failed with
      | missing absent => exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains absent (lookupExpression?_sound found))
      | form contains failed => exact sameNode _ contains ▸ failed
      | coercion contains _ failed =>
        have same := sameNode _ contains
        subst same
        rw [coercions] at failed
        cases failed
      | generalizedLocalRequirement contains otherForm _ _ _ _ _ _ _
      | generalizedLocalCoercion contains otherForm _ _ _ _ _ _ _ =>
        exact False.elim (nonlocal _ _ (sameNode _ contains ▸ otherForm))
    rw [form] at rawFault
    cases rawFault with
    | integerRequirement _ unavailable => exact False.elim (safe unavailable)

theorem left_evaluates {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {heap : Dynamic.Heap} :
    Dynamic.ExpressionEvaluates (Program.ofChecked fixture.packet.compiled.sourceProgram)
      (localContext fixture) evidence (source fixture.packet.named) environment heap
      (expressionId fixture.packet 7) (.word (Word.ofNatModulo 1)) heap :=
  numeric_evaluates fixture.parentRows.leftFound fixture.parentRows.leftForm
    fixture.parentRows.leftCoercions fixture.parentRows.leftOwned (numericLiteralValue?_sound rfl)
    (numeric_requirement (context := localContext fixture) fixture.runtime.rows (Or.inr (Or.inl rfl)))

theorem right_evaluates {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {heap : Dynamic.Heap} :
    Dynamic.ExpressionEvaluates (Program.ofChecked fixture.packet.compiled.sourceProgram)
      (localContext fixture) evidence (source fixture.packet.named) environment heap
      (expressionId fixture.packet 8) (.word (Word.ofNatModulo 2)) heap :=
  numeric_evaluates fixture.parentRows.rightFound fixture.parentRows.rightForm
    fixture.parentRows.rightCoercions fixture.parentRows.rightOwned (numericLiteralValue?_sound rfl)
    (numeric_requirement (context := localContext fixture) fixture.runtime.rows (Or.inr (Or.inr rfl)))

private theorem numeric_safe {evidence : Dynamic.EvidenceEnvironment} {number requirement : Nat}
    (member : requirement = 1 ∨ requirement = 2) :
    ¬ Dynamic.RequirementUnavailable (localContext fixture) evidence ⟨requirement⟩ := by
  have selected : NumericLiteralEvidenceReceipts.Selected numericRows
      (argumentResolution number requirement) (.builtin .intWord) := by
    rcases member with rfl | rfl
    · exact ⟨wordRequirement 1, by simp [numericRows, wordRequirement, argumentResolution], rfl, rfl⟩
    · exact ⟨wordRequirement 2, by simp [numericRows, wordRequirement, argumentResolution], rfl, rfl⟩
  exact selected.safe (context := localContext fixture) fixture.runtime.rows
    (numeric_runtime_ledger (context := localContext fixture) fixture.runtime.rows) evidence

theorem left_outcome {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (trace : Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
      (localContext fixture) evidence (source fixture.packet.named) environment before
      (expressionId fixture.packet 7) outcome after) :
    outcome = .value (.word (Word.ofNatModulo 1)) ∧ after = before :=
  numeric_outcome fixture.parentRows.leftFound fixture.runtime.source_runtime.graph.nodeOccurrencesUnique
    fixture.parentRows.leftForm fixture.parentRows.leftCoercions (numericLiteralValue?_sound rfl)
    (numeric_requirement (context := localContext fixture) fixture.runtime.rows (Or.inr (Or.inl rfl)))
    (numeric_safe fixture (number := 1) (Or.inl rfl)) trace

theorem right_outcome {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (trace : Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
      (localContext fixture) evidence (source fixture.packet.named) environment before
      (expressionId fixture.packet 8) outcome after) :
    outcome = .value (.word (Word.ofNatModulo 2)) ∧ after = before :=
  numeric_outcome fixture.parentRows.rightFound fixture.runtime.source_runtime.graph.nodeOccurrencesUnique
    fixture.parentRows.rightForm fixture.parentRows.rightCoercions (numericLiteralValue?_sound rfl)
    (numeric_requirement (context := localContext fixture) fixture.runtime.rows (Or.inr (Or.inr rfl)))
    (numeric_safe fixture (number := 2) (Or.inr rfl)) trace

/-- The actual two children execute in Source order at the same heap. -/
theorem argument_evaluates {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {heap : Dynamic.Heap} :
    Dynamic.ExpressionEvaluates (Program.ofChecked fixture.packet.compiled.sourceProgram)
      (localContext fixture) evidence (source fixture.packet.named) environment heap
      (expressionId fixture.packet 6) argumentValue heap := by
  refine .intro (raw := argumentValue) (middle := heap) (lookupExpression?_sound fixture.graph.argumentFound) ?_ ?_
  · rw [fixture.graph.argumentForm]
    exact .tuple (by simp [Dynamic.OrdinaryRequirementLayout, fixture.parentRows.argumentRequirements,
      fixture.parentRows.argumentCoercions, coercionRequirementIds])
      (.cons (left_evaluates fixture) (.cons (right_evaluates fixture) .nil)) (.cons (.singleton _))
  · rw [fixture.parentRows.argumentCoercions]
    exact .nil

private theorem children_values {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {values : List Dynamic.Value}
    (trace : Dynamic.ExpressionsEvaluate (Program.ofChecked fixture.packet.compiled.sourceProgram)
      (localContext fixture) evidence (source fixture.packet.named) environment before
      [expressionId fixture.packet 7, expressionId fixture.packet 8] values after) :
    values = [.word (Word.ofNatModulo 1), .word (Word.ofNatModulo 2)] ∧ after = before := by
  cases trace with
  | cons left tail =>
    obtain ⟨sameLeft, sameHeap⟩ := left_outcome fixture (.value left)
    cases sameHeap
    have sameValue := Dynamic.ExpressionOutcome.value.inj sameLeft
    cases sameValue
    cases tail with
    | cons right tail =>
      obtain ⟨sameRight, sameHeap⟩ := right_outcome fixture (.value right)
      cases sameHeap
      have sameValue := Dynamic.ExpressionOutcome.value.inj sameRight
      cases sameValue
      cases tail
      exact ⟨rfl, rfl⟩

private theorem children_no_fault {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (trace : Dynamic.ExpressionsFault (Program.ofChecked fixture.packet.compiled.sourceProgram)
      (localContext fixture) evidence (source fixture.packet.named) environment before
      [expressionId fixture.packet 7, expressionId fixture.packet 8] reason after) : False := by
  cases trace with
  | head failed =>
    have impossible := (left_outcome fixture (.fault failed)).1
    cases impossible
  | tail left failed =>
    have sameHeap := (left_outcome fixture (.value left)).2
    cases sameHeap
    cases failed with
    | head failed =>
      have impossible := (right_outcome fixture (.fault failed)).1
      cases impossible
    | tail _ failed => cases failed

/-- Any actual Source outcome of this pair is the same successful value at
its unchanged heap. Numeric fault exclusion uses the original complete ledger. -/
theorem argument_outcome {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (trace : Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
      (localContext fixture) evidence (source fixture.packet.named) environment before
      (expressionId fixture.packet 6) outcome after) :
    outcome = .value argumentValue ∧ after = before := by
  have sameNode : ∀ other, ContainsExpression (source fixture.packet.named) (expressionId fixture.packet 6) other →
      other = fixture.graph.argument := by
    intro other contains
    exact Option.some.inj ((lookupExpression?_complete
      fixture.runtime.source_runtime.graph.nodeOccurrencesUnique contains).symm.trans fixture.graph.argumentFound)
  have nonlocal : ∀ name binder, fixture.graph.argument.form ≠ .reference name (.local binder) := by
    intros
    rw [fixture.graph.argumentForm]
    simp
  cases trace with
  | value evaluated =>
    cases evaluated with
    | intro contains raw path =>
      have same := sameNode _ contains
      subst same
      rw [fixture.parentRows.argumentCoercions] at path
      cases path
      rw [fixture.graph.argumentForm] at raw
      cases raw with
      | tuple _ children pack =>
        obtain ⟨sameValues, sameHeap⟩ := children_values fixture children
        cases sameHeap
        rw [sameValues] at pack
        have expected : Dynamic.ValuesPack [.word (Word.ofNatModulo 1), .word (Word.ofNatModulo 2)]
            argumentValue := .cons (.singleton _)
        exact ⟨congrArg _ (pack.functional expected), rfl⟩
    | generalizedLocal contains form _ _ _ _ _ _ _ =>
      exact False.elim (nonlocal _ _ (sameNode _ contains ▸ form))
  | @fault _ _ reason failed =>
    have rawFault : Dynamic.ExpressionFormFaults (Program.ofChecked fixture.packet.compiled.sourceProgram)
        (localContext fixture) evidence (source fixture.packet.named) environment before
        fixture.graph.argument.form fixture.graph.argument.requirements fixture.graph.argument.coercions reason after := by
      cases failed with
      | missing absent => exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains absent
          (lookupExpression?_sound fixture.graph.argumentFound))
      | form contains failed => exact sameNode _ contains ▸ failed
      | coercion contains _ failed =>
        have same := sameNode _ contains
        subst same
        rw [fixture.parentRows.argumentCoercions] at failed
        cases failed
      | generalizedLocalRequirement contains form _ _ _ _ _ _ _
      | generalizedLocalCoercion contains form _ _ _ _ _ _ _ =>
        exact False.elim (nonlocal _ _ (sameNode _ contains ▸ form))
    rw [fixture.graph.argumentForm] at rawFault
    cases rawFault with
    | tuple _ failed => exact False.elim (children_no_fault fixture failed)

/-- The genuine physical pair has its raw parameter type in the receiving
closure's context, independently of any native representation. -/
theorem value_typed (context : SourceSemantics.Context) (heap : Dynamic.Heap) :
    Dynamic.ValueHasType context heap argumentValue parameterType :=
  .product (.word _) (.word _)

theorem arguments_typed (context : SourceSemantics.Context) (heap : Dynamic.Heap) :
    Dynamic.ValuesHaveTypes context heap [argumentValue] [parameterType] :=
  .cons (value_typed context heap) .nil

section Admission
universe u
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
variable {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.packet.compiled
      (Program.ofChecked fixture.packet.compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key fixture.packet.compiled
      (Program.ofChecked fixture.packet.compiled.sourceProgram))}
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

/-- The actual pair trace supplies success admission at the actual reached
state. Administrative effects carry every row's own history to that state. -/
theorem post_admission {initial reached : ProtectedStateTransition.Index}
    (first : callerProtocol.State initial) (last : callerProtocol.State reached)
    (admitted : Admission bridge (localContext fixture) first)
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment} {outcome : Dynamic.ExpressionOutcome}
    (trace : Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
      (localContext fixture) evidence (source fixture.packet.named) environment initial.heap
      (expressionId fixture.packet 6) outcome reached.heap)
    (frame : GeneralHeap.AdministrativePreserved initial.mapping initial.store reached.mapping reached.store) :
    PostAdmission bridge (localContext fixture) parameterType outcome last := by
  have same := argument_outcome fixture trace
  refine ⟨CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative
    (bridge.pool first) (bridge.pool last) admitted.rows frame, ?_⟩
  intro value isValue
  have sameValue := Dynamic.ExpressionOutcome.value.inj (isValue.symm.trans same.1)
  cases sameValue
  exact ⟨value_typed _ _, same.2 ▸ admitted.heap⟩

end Admission

end Tests.SourceCoreChosenOrdinaryAcceptedArgumentAdmission
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedOriginalProgramAdmission
/-! Original program admission from the same accepted fixture. The finite catalog
check compares complete Source records. The original checker, retained typing,
and actual specialization stage analysis supply the independent judgments. -/
set_option autoImplicit false
namespace Tests.SourceCoreChosenOrdinaryAcceptedOriginalProgramAdmission
open Solcore Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader

/-- These checks concern the original checker output, including its full Source
and ordered recursive evidence. They do not compare emitted native code. -/
structure OriginalCatalog (packet : Packet) : Prop where
  functionsChecked : (packet.program.functions == [packet.named.specialized.function]) = true
  methodsLength : packet.program.methods.length = 0

def originalCatalog (packet : Packet) : Except String (PLift (OriginalCatalog packet)) :=
  if functions : (packet.program.functions == [packet.named.specialized.function]) = true then
    if methods : packet.program.methods.length = 0 then
      .ok ⟨⟨functions, methods⟩⟩
    else .error "original checked program contains implementation methods"
  else .error "original checked function differs from the retained selected Source"

theorem OriginalCatalog.functions {packet : Packet} (given : OriginalCatalog packet) :
    packet.program.functions = [packet.named.specialized.function] :=
  LawfulBEq.eq_of_beq given.functionsChecked

theorem OriginalCatalog.methods {packet : Packet} (given : OriginalCatalog packet) :
    packet.program.methods = [] := List.length_eq_zero_iff.mp given.methodsLength

theorem OriginalCatalog.compiled_functions {packet : Packet} (given : OriginalCatalog packet) :
    packet.compiled.sourceProgram.functions = [packet.named.specialized.function] := by
  rw [(SourceCoreUnifiedPreparationCertificates.prepare_fields packet.compiledAccepted).1]
  exact given.functions

theorem OriginalCatalog.compiled_methods {packet : Packet} (given : OriginalCatalog packet) :
    packet.compiled.sourceProgram.methods = [] := by
  rw [(SourceCoreUnifiedPreparationCertificates.prepare_fields packet.compiledAccepted).1]
  exact given.methods

/-- Original worklist provenance supplies the actual original signature and
specialization equation for this same complete checked function. -/
theorem OriginalCatalog.specialization {packet : Packet} (given : OriginalCatalog packet)
    (selected : OriginalSelection packet) :
    ∃ signature : ProgramFunctionSignature, ∃ supplied : TypeSystem.ParameterSubstitution,
      signature ∈ packet.compiled.sourceProgram.signatures.functions ∧
      SourceSpecialization.specializeFunction signature packet.named.specialized.function supplied =
        .ok packet.named.specialized := by
  obtain ⟨request, signature, generic, member, genericMember, _, accepted⟩ := selected.origin packet
  rw [given.compiled_functions] at genericMember
  have same := List.mem_singleton.mp genericMember
  subst generic
  exact ⟨signature, request.parameterSubstitution, member, accepted⟩

/-- The actual empty specialization and assumptions identify the original rigid
scope; source input binders are a separate field. -/
theorem signature_fields {packet : Packet} (given : Metadata packet)
    {signature : ProgramFunctionSignature} {supplied : TypeSystem.ParameterSubstitution}
    (accepted : SourceSpecialization.specializeFunction signature packet.named.specialized.function supplied =
      .ok packet.named.specialized) :
    signature.scheme.parameters = [] ∧ signature.scheme.predicates = [] := by
  have parameters := SourceSpecialization.specializeFunction_parameterDomain accepted
  rw [given.substitution, List.map_nil] at parameters
  have predicates := (CallableCoercionBodyProvenance.specialization_fields accepted).2
  rw [given.assumptions] at predicates
  exact ⟨parameters.symm, List.map_eq_nil_iff.mp predicates.symm⟩

theorem original_context {packet : Packet} (given : Metadata packet)
    {signature : ProgramFunctionSignature} {supplied : TypeSystem.ParameterSubstitution}
    (accepted : SourceSpecialization.specializeFunction signature packet.named.specialized.function supplied =
      .ok packet.named.specialized) :
    checkedBodyContext packet.compiled.sourceProgram.signatures signature packet.named.specialized.function =
      runtimeContext packet := by
  obtain ⟨parameters, predicates⟩ := signature_fields given accepted
  have identities := RecursiveNamedSpecializationBodyFacts.identities accepted
  have owner : signature.id = (CallableIndexedNamedGeneration.source packet.named).owner :=
    identities.1.trans identities.2.1.symm
  simp only [checkedBodyContext, runtimeContext, parameters, predicates, owner]

/-- All original bodies are typed using the retained finite body proof, at the
original checker's fuel. No global recursive inference theorem is assumed. -/
theorem statements_typed {fixture : AcceptedFixture} (catalog : OriginalCatalog fixture.packet)
    (selected : OriginalSelection fixture.packet) (given : Metadata fixture.packet)
    (lambda : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
    (outer : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata fixture) :
    CheckedProgramBodiesHaveStatementTyping fixture.packet.program 1024 := by
  obtain ⟨signature, supplied, signatureMember, accepted⟩ := catalog.specialization selected
  have programEq := (SourceCoreUnifiedPreparationCertificates.prepare_fields fixture.packet.compiledAccepted).1
  have originalMember : signature ∈ fixture.packet.program.signatures.functions := by
    rwa [programEq] at signatureMember
  have functionMember : fixture.packet.named.specialized.function ∈ fixture.packet.program.functions := by
    rw [catalog.functions]
    exact List.mem_singleton_self _
  obtain ⟨headerSignature, headerMember, header⟩ :=
    checkedFunctionHeaderWellFormed_ofCheckProgram fixture.packet.checked functionMember
  have unique := (SignatureCatalogWellFormed.ofCheckProgram fixture.packet.checked).function_ids
  have identities := RecursiveNamedSpecializationBodyFacts.identities accepted
  have headerEq : headerSignature = signature := eq_of_mem_of_nodup_map unique
    headerMember originalMember (header.declaration_eq.symm.trans identities.1.symm)
  subst headerSignature
  have inputs : fixture.packet.named.specialized.function.typedBody.inputs = [] := given.inputs
  obtain ⟨_, extension⟩ := header.inputs_extend
  have length := extension.length_eq
  rw [inputs, List.length_nil] at length
  have parameterTypes : signature.parameterTypes = [] := List.length_eq_zero_iff.mp length.symm
  have resultType : TypeSystem.Ty.productMany signature.returnTypes = wordType :=
    header.result_type.symm.trans outer.resultType
  have contextEq : checkedBodyContext fixture.packet.program.signatures signature
      fixture.packet.named.specialized.function = runtimeContext fixture.packet := by
    rw [← programEq]
    exact original_context given accepted
  constructor
  · intro function member candidate candidateMember bodyAccepted
    rw [catalog.functions] at member
    have same := List.mem_singleton.mp member
    subst function
    have candidateEq : candidate = signature := eq_of_mem_of_nodup_map unique
      candidateMember originalMember
      ((checkFunctionBody_success_declaration bodyAccepted).symm.trans identities.1.symm)
    subst candidate
    intro statements roots
    have mapped : statements.map NodeId.statement =
        [statementId fixture.packet 0, statementId fixture.packet 4].map NodeId.statement :=
      roots.symm.trans fixture.graph.roots
    have statementsEq : statements = [statementId fixture.packet 0, statementId fixture.packet 4] :=
      (List.map_inj_right (by intro a b same; cases same; rfl)).mp mapped
    subst statements
    refine ⟨SourceCoreChosenOrdinaryAcceptedOuterTyping.bodyFacts, resultType.symm, ?_⟩
    intro lexicalContext extended
    rw [inputs, parameterTypes] at extended
    cases extended
    refine ⟨SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture, ?_⟩
    rw [contextEq, resultType]
    exact SourceCoreChosenOrdinaryAcceptedOuterTyping.body_typed lambda outer
  · intro method member
    rw [catalog.methods] at member
    cases member

theorem program_well_formed {fixture : AcceptedFixture} (catalog : OriginalCatalog fixture.packet)
    (selected : OriginalSelection fixture.packet) (given : Metadata fixture.packet)
    (lambda : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
    (outer : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata fixture) :
    ProgramWellFormed (Program.ofChecked fixture.packet.compiled.sourceProgram) := by
  rw [(SourceCoreUnifiedPreparationCertificates.prepare_fields fixture.packet.compiledAccepted).1]
  exact programWellFormed_ofCheckProgram_statements fixture.packet.checked
    (statements_typed catalog selected given lambda outer)

/-- The retained successful stage analysis classifies the same original sole
function. Empty method membership closes the remaining original catalog. -/
theorem program_has_stages {fixture : AcceptedFixture} (catalog : OriginalCatalog fixture.packet)
    (selected : OriginalSelection fixture.packet) (given : Metadata fixture.packet)
    (lambda : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
    (outer : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata fixture) :
    Staging.ProgramHasStages (Program.ofChecked fixture.packet.compiled.sourceProgram) := by
  refine ⟨program_well_formed catalog selected given lambda outer, ?_, ?_⟩
  · intro definition member
    obtain ⟨function, functionMember, rfl⟩ := List.mem_map.mp member
    rw [catalog.compiled_functions] at functionMember
    have same := List.mem_singleton.mp functionMember
    subst function
    obtain ⟨_, _, _, accepted⟩ := catalog.specialization selected
    have originalMember : fixture.packet.named.specialized.function ∈ fixture.packet.program.functions := by
      rw [catalog.functions]
      exact List.mem_singleton_self _
    obtain ⟨_, _, bodyAccepted⟩ := checkProgram_success_function_body fixture.packet.checked originalMember
    change Staging.BodyDefinitionHasStages (BodyDefinition.ofChecked fixture.packet.named.specialized.function)
    exact (Staging.bodyDefinitionOfChecked_iff _).2
      (SourceStageAnalysisSoundness.checkFunctionBody_analysis_success_hasStages bodyAccepted
        (RecursiveNamedSpecializationStageFacts.analyzed accepted))
  · intro definition member
    change definition ∈ fixture.packet.compiled.sourceProgram.methods.map MethodDefinition.ofChecked at member
    rw [catalog.compiled_methods] at member
    cases member

end Tests.SourceCoreChosenOrdinaryAcceptedOriginalProgramAdmission
end
