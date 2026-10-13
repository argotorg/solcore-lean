import Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodRootSupport
import Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodRuntimeProfileFactory
import Solcore.SourceSemantics.CoreLowering.RecursiveMethodPreparedStageScopes
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalBodyTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCompilerPolicyProfiles

/-! Static terminal method packets retain the genuine trait principal, exact
parameter context and original accepted body. The selected instance certificate and
the actual compiler callback provide the used child; no execution law is stored. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodBodySupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedMethodPrincipal (Principal)
open CallablePreparedMethodRuntimeProfileFactory (SourceAt policy scope)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt Terminal)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {method : ExecutableImplMethods.CheckedMethod}
  (principal : Principal compiled method)

def Certified (sourceAt : SourceAt principal.cached.compilation (.initial compiled.compatible.checked)
    principal.sourceBody principal.dictionary) : Prop :=
  ∃ facts, Dynamic.BodyInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
    principal.sourceBody sourceAt.types sourceAt.context facts

/-- The actual selector contributes only its own retained method certificate. -/
theorem Certified.of_typed
    (sourceAt : SourceAt principal.cached.compilation (.initial compiled.compatible.checked)
      principal.sourceBody principal.dictionary)
    {context : SourceSemantics.Context} {caller : Dynamic.EvidenceEnvironment}
    {traitName methodName : String} {requirements : List RequirementId}
    (selected : Dynamic.TypedOperatorMethodSelected (Program.ofChecked compiled.sourceProgram)
      context caller traitName methodName requirements principal.sourceBody principal.dictionary) :
    Certified principal sourceAt := by
  cases selected with
  | intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ certificate =>
    obtain ⟨types, lexical, facts, typed⟩ := certificate
    have contextEq := Dynamic.MonoBindersExtend.functional typed.typing.inputs_extend sourceAt.extended
    have typesEq := (Dynamic.MonoBindersExtend.bodyTypes_eq typed.typing.inputs_extend).symm.trans
      (Dynamic.MonoBindersExtend.bodyTypes_eq sourceAt.extended)
    exact ⟨facts, typesEq ▸ contextEq ▸ typed.toBodyInstanceTypingCertificate⟩

structure Packet where
  sourceAt : SourceAt principal.cached.compilation (.initial compiled.compatible.checked)
    principal.sourceBody principal.dictionary
  expression : ExpressionId
  receipt : Receipt (policy principal.cached.compilation) compiled.indexed.fuel principal.sourceBody.source
    (scope (named := principal.named)) expression principal.cached.compilation.statements
    principal.named.signature.resultType (principal.cached.diagnostics.reasonAt principal.named.signature.key)
    principal.cached.compilation.own.fellThroughReason principal.cached.compilation.own.table.escapedReason
    principal.cached.compilation.body

/-- The actual selected Source method determines typing in the same parameter
context retained by SourceAt; native type projection is not used for this step. -/
theorem source_typing (sourceAt : SourceAt principal.cached.compilation (.initial compiled.compatible.checked)
    principal.sourceBody principal.dictionary)
    (certified : Certified principal sourceAt) :
    ∃ facts, Dynamic.BodyInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
      principal.sourceBody sourceAt.types sourceAt.context facts := by
  exact certified

theorem statements (packet : Packet principal)
    (certified : Certified principal packet.sourceAt) :
    ∃ final facts, StatementsHaveType principal.sourceBody.source {returnType := principal.sourceBody.resultType}
      packet.sourceAt.context principal.cached.compilation.statements final facts ∧
      BodyCompletes principal.sourceBody.resultType facts := by
  obtain ⟨facts, typed⟩ := source_typing principal packet.sourceAt certified
  obtain ⟨final, body, _roots, complete⟩ := typed.typing.body_typed
  refine ⟨final, facts, ?_, complete⟩
  have roots : (principal.sourceBody.source.roots.filterMap fun root => match root with
      | .statement statement => some statement | .expression _ => none) = principal.cached.compilation.statements :=
    principal.source_frame.roots.filterMap_eq
  exact roots ▸ body

/-- Original Source typing selects the actual terminal expression and raw result. -/
theorem child_typed (packet : Packet principal)
    (certified : Certified principal packet.sourceAt)
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure principal.sourceFunction child) :
    ∃ node, child.source.lookupExpression? packet.expression = some node ∧
      node.type = principal.sourceBody.resultType ∧
      ExpressionHasType child.source packet.sourceAt.context packet.expression node.type := by
  have sourceEq : child.source = principal.sourceBody.source := stages.source selected
  obtain ⟨final, facts, typed, complete⟩ := statements principal packet certified
  rw [← sourceEq] at typed
  exact CallableIndexedOwnedPreparedStagedTerminalBodyTyping.child_typed
    (sourceEq ▸ packet.sourceAt.unique) (packet.receipt.head child sourceEq) typed complete

/-- Static validity is transported along the genuine method parameter extension. -/
theorem runtime (packet : Packet principal)
    (certified : Certified principal packet.sourceAt) :
    Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      packet.sourceAt.context principal.sourceBody.source := by
  obtain ⟨_facts, typed⟩ := source_typing principal packet.sourceAt certified
  exact typed.sourceRuntimeValid.transport (RecursiveNamedInitialContextValidity.mono_fields packet.sourceAt.extended)

/-- The exact contextual compiler action selects one shared policy for the
method child, preserving the actual specializer row and callback budget. -/
theorem policy_receipt (packet : Packet principal) :
    ∃ fuel, Nonempty (CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt (compiled := compiled)
      principal.named principal.cached.diagnostics principal.cached.code principal.cached.compilation
      fuel principal.sourceBody.source (scope (named := principal.named)) packet.expression
      (principal.cached.diagnostics.reasonAt principal.named.signature.key) packet.receipt.child) := by
  have accepted := packet.receipt.generated
  change SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
    ((CallableIndexedNamedGeneration.representation compiled.indexed).atContext principal.named.signature.key [])
    compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.locals
    principal.cached.compilation.parents principal.cached.compilation.own.assignments principal.cached.diagnostics
    (CallableIndexedNamedGeneration.context compiled.indexed principal.named)
    compiled.indexed.base.callableContext none none packet.receipt.childFuel principal.sourceBody.source
    (scope (named := principal.named)) packet.expression
    (principal.cached.diagnostics.reasonAt principal.named.signature.key) = .ok packet.receipt.child at accepted
  cases eq : packet.receipt.childFuel with
  | zero =>
    rw [eq, SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted
    cases accepted
  | succ fuel =>
    exact ⟨fuel, CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt.of_accepted
      principal.cached.compilation principal.record (by simpa only [eq] using accepted)⟩

/-- Only the actual original terminal syntax is needed in addition to SourceAt. -/
theorem of_terminal
    (sourceAt : SourceAt principal.cached.compilation (.initial compiled.compatible.checked)
      principal.sourceBody principal.dictionary)
    (expression : ExpressionId)
    (terminal : Terminal principal.sourceBody.source expression principal.cached.compilation.statements) :
    Nonempty (Packet principal) := by
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    (by rfl) terminal sourceAt.accepted
  exact ⟨⟨sourceAt, expression, receipt⟩⟩

/-- The selected root keeps the method result, diagnostic issuer and real
single packed-argument prefix. Called-body meaning is supplied by the numeric IH. -/
structure Child (packet : Packet principal)
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)))
    (stages : Staging.Recursive.Registry) (child : Staging.Recursive.Scope)
    (semanticFaults : FunctionCalls.FaultRep) extends
    SelectedCompilationMethodRootSupport.RootAt compiled headers stages
      packet.sourceAt.context child (scope (named := principal.named)) packet.expression
      packet.receipt.child semanticFaults where
  result : rawType = principal.sourceBody.resultType
  reasons : reasonAt = principal.cached.diagnostics.reasonAt principal.named.signature.key
  prefixLength : compilation.administrativePrefix = 1

/-- Every actual selected method scope receives a static expression root. -/
structure Support (packet : Packet principal)
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)))
    (stages : Staging.Recursive.Registry) (semanticFaults : FunctionCalls.FaultRep) : Prop where
  roots : ∀ child, stages.Closure principal.sourceFunction child →
    Nonempty (Child principal packet headers stages child semanticFaults)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodBodySupport
