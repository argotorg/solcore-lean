import Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodBodySupport
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationMixedRootSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingTree
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBranchingCatalogSites

/-! Scoped method packets retain the actual selected implementation, complete
Source dictionary, parameter context and accepted flow. Reached children keep
their original lexical fields and mixed expression roots. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodScopedSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedMethodPrincipal (Principal)
open CallablePreparedMethodRuntimeProfileFactory (SourceAt policy scope)
open CompatibleEncoding (bind_ok)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {method : ExecutableImplMethods.CheckedMethod}
  (principal : Principal compiled method)

abbrev parameterScope : SourceCoreLocalCell.Scope := scope (named := principal.named)

def nativePrefix : Core.Context :=
  principal.named.signature.parameterType :: compiled.indexed.base.globals.map (·.referenceType) ++
    [.cell compiled.indexed.ancestry.layout.frame.type]

structure Packet where
  sourceAt : SourceAt principal.cached.compilation (.initial compiled.compatible.checked)
    principal.sourceBody principal.dictionary
  flow : Expr
  accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy (policy principal.cached.compilation)
    compiled.indexed.fuel principal.sourceBody.source (parameterScope principal)
    principal.cached.compilation.statements principal.named.signature.resultType
    (principal.cached.diagnostics.reasonAt principal.named.signature.key) true
    principal.cached.compilation.own.table.escapedReason = .ok flow
  emitted : principal.cached.compilation.body = CompatibleStatements.finish
    principal.named.signature.resultType flow principal.cached.compilation.own.fellThroughReason
    principal.cached.compilation.own.table.escapedReason
  shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape principal.sourceBody.source true
    principal.cached.compilation.statements

/-- The real accepted method body determines its flow without any execution premise. -/
theorem of_accepted
    (sourceAt : SourceAt principal.cached.compilation (.initial compiled.compatible.checked)
      principal.sourceBody principal.dictionary)
    (shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape principal.sourceBody.source true
      principal.cached.compilation.statements) : Nonempty (Packet principal) := by
  have accepted := sourceAt.accepted principal.cached.compilation
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, returned⟩ := bind_ok accepted
  exact ⟨⟨sourceAt, flow, generated, (Except.ok.inj returned).symm, shape⟩⟩

theorem statements (packet : Packet principal)
    (certified : SelectedCompilationMethodBodySupport.Certified principal packet.sourceAt) :
    ∃ final facts, StatementsHaveType principal.sourceBody.source {returnType := principal.sourceBody.resultType}
      packet.sourceAt.context principal.cached.compilation.statements final facts ∧
      BodyCompletes principal.sourceBody.resultType facts := by
  obtain ⟨facts, typed⟩ := SelectedCompilationMethodBodySupport.source_typing
    principal packet.sourceAt certified
  obtain ⟨final, body, _roots, complete⟩ := typed.typing.body_typed
  refine ⟨final, facts, ?_, complete⟩
  have roots : (principal.sourceBody.source.roots.filterMap fun root => match root with
      | .statement statement => some statement | .expression _ => none) = principal.cached.compilation.statements :=
    principal.source_frame.roots.filterMap_eq
  exact roots ▸ body

theorem runtime (packet : Packet principal)
    (certified : SelectedCompilationMethodBodySupport.Certified principal packet.sourceAt) :
    Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      packet.sourceAt.context principal.sourceBody.source := by
  obtain ⟨_facts, typed⟩ := SelectedCompilationMethodBodySupport.source_typing
    principal packet.sourceAt certified
  exact typed.sourceRuntimeValid.transport (RecursiveNamedInitialContextValidity.mono_fields packet.sourceAt.extended)

abbrev Certificate
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)))
    (stages : Staging.Recursive.Registry) (semanticFaults : FunctionCalls.FaultRep)
    (context : SourceSemantics.Context) (invocation : Staging.Recursive.Scope)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) : Prop :=
  ∃ root : SelectedCompilationMixedRootSupport.RootAt compiled headers stages
      context invocation scope id lowered semanticFaults,
    root.compilation.administrativePrefix = 1

structure Support (packet : Packet principal)
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)))
    (stages : Staging.Recursive.Registry) (semanticFaults : FunctionCalls.FaultRep) : Prop where
  tree : ∀ child, stages.Closure principal.sourceFunction child →
    ∃ expressionSyntax : ExpressionId → Prop,
      CallableIndexedOwnedPreparedBranchingCatalogSites.Collected (faults := semanticFaults) compiled.indexed.layouts
        principal.named.signature.key [] compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
        (fun error => .sourceAllocation (reprStr error)) (.initial compiled.compatible.checked)
        child.source expressionSyntax
        (CallableIndexedOwnedPreparedStagedLexicalTree.TypedCertificate child.source
          (fun context => Certificate headers stages semanticFaults context child))
        compiled.indexed.layouts.definitions (nativePrefix principal)
        packet.sourceAt.context (parameterScope principal) (.statements true principal.cached.compilation.statements)
        principal.sourceBody.resultType principal.named.signature.resultType packet.flow

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodScopedSupport
