import Solcore.Test.SourceCoreMethodScopedInventory
import Solcore.Test.SourceCoreMethodScopedCatalog
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodTerminalSupport

/-! Every selected method uses the actual original method table. Structural
Source instantiation transports its read-and-return syntax; the real compiler
and staged selector supply all typing, dictionary and cache authority. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreMethodScoped
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedMethodTerminalSupport (ReadOnlySource)

structure MethodReadBody (source : TypedSource) where
  expression : ExpressionNode
  statement : StatementNode
  name : String
  binder : Resolved.LocalId
  nodes : source.nodes = [.expression expression, .statement statement]
  roots : source.roots = [.statement statement.id]
  read : expression.form = .reference name (.local binder)
  returned : statement.form = .returnStmt (some expression.id)
  requirements : expression.requirements = []
  coercions : expression.coercions = []
  distinct : expression.id.occurrence ≠ statement.id.occurrence

namespace MethodReadBody
variable {source : TypedSource} (shape : MethodReadBody source)

theorem expression_found : source.lookupExpression? shape.expression.id = some shape.expression := by
  simp [TypedSource.lookupExpression?, TypedSource.lookupNode?, shape.nodes, Node.occurrenceId, Node.id, NodeId.occurrenceId]

theorem statement_found : source.lookupStatement? shape.statement.id = some shape.statement := by
  simp [TypedSource.lookupStatement?, TypedSource.lookupNode?, shape.nodes, Node.occurrenceId, Node.id, NodeId.occurrenceId, shape.distinct]

include shape in
theorem only_reads : ReadOnlySource source := by
  intro id node found
  have member := (lookupExpression?_sound found).1
  rw [shape.nodes] at member
  simp only [List.mem_cons, List.not_mem_nil, Node.expression.injEq, reduceCtorEq, or_false] at member
  subst node
  exact ⟨shape.name, shape.binder, shape.read⟩

/-- Rigid substitution retains the exact read/return graph and occurrence IDs. -/
def substituted (substitution : TypeSystem.ParameterSubstitution) :
    MethodReadBody (StructuralSubstitution.applyTypedSource substitution source) where
  expression := StructuralSubstitution.applyExpressionNode substitution shape.expression
  statement := StructuralSubstitution.applyStatementNode substitution shape.statement
  name := shape.name
  binder := shape.binder
  nodes := by simp [StructuralSubstitution.applyTypedSource, shape.nodes, StructuralSubstitution.applyNode]
  roots := shape.roots
  read := by simp [StructuralSubstitution.applyExpressionNode, shape.read,
    StructuralSubstitution.applyExpressionForm, StructuralSubstitution.applyReferenceResolution]
  returned := by simp [StructuralSubstitution.applyStatementNode, shape.returned, StructuralSubstitution.applyStatementForm, StructuralSubstitution.applyExpressionNode]
  requirements := shape.requirements
  coercions := by simp [StructuralSubstitution.applyExpressionNode, shape.coercions]
  distinct := shape.distinct
end MethodReadBody

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

def observeMethodReadBody (source : TypedSource) : IO (MethodReadBody source) := do
  let [.expression expression, .statement statement] := source.nodes | throw (IO.userError "method original read body")
  let .reference name (.local binder) := expression.form | throw (IO.userError "method original read")
  let ⟨nodes⟩ ← observed (source.nodes = [.expression expression, .statement statement]) "method nodes"
  let ⟨roots⟩ ← observed (source.roots = [.statement statement.id]) "method roots"
  let ⟨read⟩ ← observed (expression.form = .reference name (.local binder)) "method read form"
  let ⟨returned⟩ ← observed (statement.form = .returnStmt (some expression.id)) "method return form"
  let ⟨requirements⟩ ← observed (expression.requirements = []) "method read requirements"
  let ⟨coercions⟩ ← observed (expression.coercions = []) "method read coercions"
  let ⟨distinct⟩ ← observed (expression.id.occurrence ≠ statement.id.occurrence) "method distinct occurrences"
  return {expression, statement, name, binder, nodes, roots, read, returned, requirements, coercions, distinct}

structure MethodBodies (fixture : CompiledFixture) : Prop where
  bodies : ∀ definition, definition ∈ (Program.ofChecked fixture.recipe.compiled.sourceProgram).methods →
    Nonempty (MethodReadBody definition.body.source)

private def observeMethodBodyList : (methods : List MethodDefinition) →
    IO (PLift (∀ definition, definition ∈ methods → Nonempty (MethodReadBody definition.body.source)))
  | [] => pure ⟨by intro definition member; cases member⟩
  | first :: rest => do
    let shape ← observeMethodReadBody first.body.source
    let ⟨tail⟩ ← observeMethodBodyList rest
    return ⟨by
      intro definition member
      rcases List.mem_cons.mp member with same | member
      · exact same ▸ ⟨shape⟩
      · exact tail definition member⟩

def observeMethodBodies (fixture : CompiledFixture) : IO (PLift (MethodBodies fixture)) := do
  let ⟨bodies⟩ ← observeMethodBodyList (Program.ofChecked fixture.recipe.compiled.sourceProgram).methods
  return ⟨⟨bodies⟩⟩

/-- Only the independent actual method-instantiation relation is used to
select the original source body. The compiler cache never becomes a fake Header. -/
theorem MethodBodies.selected {fixture : CompiledFixture} (bodies : MethodBodies fixture)
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal fixture.recipe.compiled method) :
    Nonempty (MethodReadBody principal.sourceBody.source) := by
  obtain ⟨implementation, declaration, trait, definition, substitution, instantiated⟩ := principal.source_instantiation
  cases instantiated with
  | intro _implementation _method _trait _owner member _id _bodyOwner _exact _range source _result _context =>
    obtain ⟨shape⟩ := bodies.bodies definition member
    exact source ▸ ⟨shape.substituted substitution⟩

/-- Each genuinely selected method receives the actual terminal packet and a
static root. Only original syntax is inspected; the actual SourceAt and cache
retain typing, parameter allocation, dictionary and diagnostic authority. -/
theorem MethodBodies.support {fixture : CompiledFixture} (bodies : MethodBodies fixture)
    (observed : ObservedProgram fixture)
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal fixture.recipe.compiled method)
    (sourceAt : CallablePreparedMethodRuntimeProfileFactory.SourceAt principal.cached.compilation
      (.initial fixture.recipe.compiled.compatible.checked) principal.sourceBody principal.dictionary)
    (diagnostic : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt principal.cached)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)))
    (stages : Staging.Recursive.Registry) :
    ∃ packet : CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport.Packet principal,
      packet.sourceAt = sourceAt ∧
      CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport.Support principal packet headers stages
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
  obtain ⟨shape⟩ := bodies.selected principal
  have statements : principal.cached.compilation.statements = [shape.statement.id] := by
    have roots : (principal.sourceBody.source.roots.filterMap fun root => match root with
        | .statement statement => some statement | .expression _ => none) = principal.cached.compilation.statements :=
      principal.source_frame.roots.filterMap_eq
    rw [shape.roots] at roots
    simpa using roots.symm
  have terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      principal.sourceBody.source shape.expression.id principal.cached.compilation.statements := by
    rw [statements]
    exact .returning [] shape.statement_found shape.returned
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    (by rfl) terminal sourceAt.accepted
  let packet : CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport.Packet principal :=
    ⟨sourceAt, shape.expression.id, receipt⟩
  refine ⟨packet, rfl, ?_⟩
  exact CallableIndexedOwnedPreparedStagedMethodTerminalSupport.of_read
    principal diagnostic receiver packet fixture.source_wellFormed shape.only_reads
    shape.expression_found shape.read shape.requirements shape.coercions
    (by simp [observed.noLocals]) (by simp [observed.noLocals])

end Tests.SourceCoreMethodScoped
