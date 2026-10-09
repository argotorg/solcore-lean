import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedMixedBodySiteInputs
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedMixedBodyRuntimeBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedActualNamedSourceReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLiteralReturnSiteShells
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFiniteSourceRuntimeReceipts
import Solcore.Test.SourceCompilerFeatureSupport

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
