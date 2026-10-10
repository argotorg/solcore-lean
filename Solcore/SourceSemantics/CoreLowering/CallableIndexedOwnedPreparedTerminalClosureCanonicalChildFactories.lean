import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalClosureFactories

/-! The original Source compiler Tree retains the exact terminal child beside
its actual compiler-view certificate. Statement metadata transports only the
terminal form. Accepted finish equality identifies the same lowered child;
no equality of whole Sources, expression types or coercions is inferred. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalClosureCanonicalChildFactories
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedLambdaStaticBodySupport
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Terminal)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedTerminalClosureFactories

private theorem lowered_eq {left right : SourceCoreBasic.LoweredExpr}
    (sameType : left.type = right.type) (sameExpression : left.expression = right.expression) :
    left = right := by
  cases left
  cases right
  cases sameType
  cases sameExpression
  rfl

private theorem finish_injective {type : Ty} {left right : Expr} {leftFellThrough leftEscaped rightFellThrough rightEscaped : Word}
    (same : CompatibleStatements.finish type left leftFellThrough leftEscaped =
      CompatibleStatements.finish type right rightFellThrough rightEscaped) : left = right := by
  unfold CompatibleStatements.finish LocalControl.finish LocalLoop.toControl LanguageResult.bind at same
  exact (Expr.caseE.inj (Expr.caseE.inj same).1).1

private theorem return_value_injective {type : Ty} {left right : Expr}
    (same : LocalLoop.returnValue type left = LocalLoop.returnValue type right) : left = right := by
  unfold LocalLoop.returnValue LanguageResult.bind at same
  exact (Expr.caseE.inj same).1

section StaticTrees
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context}
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {expression : ExpressionId} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {flow : Expr}

private theorem lexical_terminal_child
    (terminal : Terminal source expression statements)
    (tree : GenericLexicalStatements.Tree layouts owner active frame globals onError values source
      certificates context scope true statements expected type flow) :
    ∃ lowered : SourceCoreBasic.LoweredExpr, lowered.type = type ∧
      flow = LocalLoop.returnValue type lowered.expression ∧
      certificates context scope expression lowered := by
  cases terminal with
  | returning rest found form =>
    cases tree <;> try simp_all
    all_goals exact ⟨_, rfl, rfl, by assumption⟩
  | tail found form =>
    cases tree <;> try simp_all
    all_goals exact ⟨_, rfl, rfl, by assumption⟩

private theorem imperative_terminal_child
    (terminal : Terminal source expression statements)
    (tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values source
      expressionSyntax certificates definitions administrative context scope
      (.statements true statements) expected type flow) :
    ∃ lowered : SourceCoreBasic.LoweredExpr, lowered.type = type ∧
      flow = LocalLoop.returnValue type lowered.expression ∧
      certificates context scope expression lowered := by
  cases tree
  case body syntaxTree body => exact lexical_terminal_child terminal body
  all_goals cases terminal <;> simp_all
end StaticTrees

private theorem terminal_on_source {original view : TypedSource}
    {expression : ExpressionId} {statements : List StatementId}
    (metadata : LambdaMetadataViews.MetadataView original view)
    (terminal : Terminal view expression statements) : Terminal original expression statements := by
  cases terminal with
  | returning rest found form => exact .returning rest (metadata.statement found) form
  | tail found form => exact .tail (metadata.statement found) form

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {code : Code compiled.indexed function scope administrative}
  {expressionSyntax : TypedSource → ExpressionId → Prop}
  {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {registry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {stages : Staging.Recursive.Registry}

private abbrev bodyScope {closure : Dynamic.Closure}
    {localScope : SourceCoreLocalCell.Scope} {admin : Core.Context}
    (code : Code compiled.indexed closure localScope admin) : SourceCoreLocalCell.Scope :=
  code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ localScope

/-- The retained original Source Tree certifies the same lowered child as
this actual terminal packet. The body flow is the real common static witness. -/
theorem canonical_child
    (body : BodyWith (values := .initial compiled.compatible.checked) expressionSyntax certificates code
      (Program.ofChecked compiled.sourceProgram) registry semanticFaults)
    (expression : ExpressionId) (terminal : Terminal code.view expression function.body)
    (packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages) :
    certificates body.readFuel function.source body.toContext.context
      (bodyScope code) expression packet.receipt.child := by
  have originalTerminal : Terminal function.source expression function.body :=
    terminal_on_source code.viewOfSource terminal
  obtain ⟨lowered, sameType, flow, certified⟩ := imperative_terminal_child originalTerminal body.tree
  have sameFlow : body.flow = LocalLoop.returnValue code.receipt.resultCore packet.receipt.child.expression :=
    finish_injective (body.emitted.symm.trans packet.receipt.emitted)
  have sameExpression : lowered.expression = packet.receipt.child.expression :=
    return_value_injective (flow.symm.trans sameFlow)
  have sameLowered : lowered = packet.receipt.child :=
    lowered_eq (sameType.trans packet.receipt.sameType.symm) sameExpression
  exact sameLowered ▸ certified

variable
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {mapping : LocationMap} {world : StoreTyping} {native : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}

/-- The canonical Source child is indexed by the same physical expression and
lowered compiler child; the complete original certificate family stays static. -/
def HasCanonicalBodyChild
    (association : Association headers keys registry semanticFaults mapping world function native
      bindings parameterCore resultCore) (expression : ExpressionId)
    (packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.TerminalFor association stages) : Prop :=
  match association, packet with
  | .ordinary _ _ code _ support _ _ _ _ _ _, packet =>
      packet.expression = expression ∧
      support.certificates support.body.readFuel function.source support.body.toContext.context
        (bodyScope code) expression packet.receipt.child
  | .principal _ _ code _ support _ _ _ _ _ _, packet =>
      packet.expression = expression ∧
      support.certificates support.body.readFuel function.source support.body.toContext.context
        (bodyScope code) expression packet.receipt.child

/-- This uses the actual child already exposed by the same-Code factory and
adds the original Source Tree's exact certificate without a transport premise. -/
theorem canonical_for
    (association : Association headers keys registry semanticFaults mapping world function native
      bindings parameterCore resultCore) (expression : ExpressionId)
    (terminal : TerminalShapeFor association expression)
    (packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.TerminalFor association stages)
    (actualChild : HasBodyChild association expression packet) :
    HasCanonicalBodyChild association expression packet := by
  cases association with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
    change _ ∧ packet.expression = expression ∧ _ at actualChild
    exact ⟨actualChild.2.1, canonical_child support.body expression terminal packet⟩
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    change _ ∧ packet.expression = expression ∧ _ at actualChild
    exact ⟨actualChild.2.1, canonical_child support.body expression terminal packet⟩

/-- The accepted factory retains both the actual-view and canonical-Source
child certificates for the same requested expression and selected scope. -/
theorem terminal_for_both
    (association : Association headers keys registry semanticFaults mapping world function native
      bindings parameterCore resultCore) (expression : ExpressionId)
    (terminal : TerminalShapeFor association expression) (reader : ReadPolicyFor association)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    ∃ packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.TerminalFor association stages,
      HasBodyChild association expression packet ∧ HasCanonicalBodyChild association expression packet := by
  obtain ⟨packet, actualChild⟩ := terminal_for_exact association expression terminal reader child selected
  exact ⟨packet, actualChild, canonical_for association expression terminal packet actualChild⟩

/-- Real descriptor/Source authority still selects the staged child internally.
The extra canonical child certificate requires no registry totality assumption. -/
theorem at_prepared_registry_both
    (association : Association headers keys registry semanticFaults mapping world function native
      bindings parameterCore resultCore) (expression : ExpressionId)
    (terminal : TerminalShapeFor association expression) (reader : ReadPolicyFor association) :
    ∃ packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.TerminalFor association
      (RecursiveStageRegistry.registry compiled.sourceProgram compiled.indexed.base.plan
        compiled.indexed.ancestry.graph.inputs.callable.table),
      HasBodyChild association expression packet ∧ HasCanonicalBodyChild association expression packet := by
  obtain ⟨packet, actualChild⟩ := at_prepared_registry_exact association expression terminal reader
  exact ⟨packet, actualChild, canonical_for association expression terminal packet actualChild⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalClosureCanonicalChildFactories
