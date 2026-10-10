import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLiteralIssuedSourceReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualDiagnosticSources
import Solcore.SourceSemantics.CoreLowering.SourceDiagnosticTypingOrigins

/-! A positive issuer packet comes from the exact sealed second-pass slot.
The original compatible diagnostics, named compiler action, selected assignment
row and complete Source are retained together. Ordinary and selected-method
packets use the same genuine factory; a synthetic method has no ordinary Header.

An arbitrary older IssuedSource may have been prepared at another first token.
This producer does not upgrade that packet or infer diagnostic identity from
equal native code. Prospective collectors must retain the issued packet and
Compilation produced here. Transfer of an actual operand/unary occurrence to
the receiving diagnostic table still needs the real program/fixed-prefix
priority producer and successful receiving-registry rebuild.
-/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedDiagnosticIssuerReceipts
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualLambdaSourceDiagnostics
open CallableIndexedOwnedLiteralPlaceDiagnosticShells

/-- Only the actual callable receiver replacement changes the lowered table. -/
def lowered (compiled : SourceCoreUnifiedCompilation.Compiled)
    (diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)) :
    SourceCoreDataPlaceFaultSites.Program :=
  match compiled.indexed.base.callableContext with
  | none => diagnostics.program
  | some native => {diagnostics.program with rootTable := native.diagnostics.rootTable}

/-- The full-key selector retains the original complete Source in the plan. -/
theorem selected_collected {compiled : SourceCoreUnifiedCompilation.Compiled} {named : Named}
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan
      named.signature.key = .ok named.specialized) :
    (named.signature.key, source named) ∈ compiled.indexed.base.plan.specializations.map
      (fun specialized => (specialized.key, specialized.function.typedBody)) := by
  have member : named.specialized ∈ compiled.indexed.base.plan.specializations.filter
      (fun actual => decide (actual.key = named.signature.key)) := by
    rw [CallableIndexedOwnedContextualDiagnosticSources.selected_filter record]
    exact List.mem_singleton_self _
  exact List.mem_map.mpr ⟨named.specialized, (List.mem_filter.mp member).1, by
    rw [CallableIndexedOwnedContextualDiagnosticSources.selected_key record]
    rfl⟩

/-- These are actual compiler records. The issuer's table equality is an output
of the factory, alongside the genuine cache slot and diagnostic identity. -/
structure SelectedReceipt (compiled : SourceCoreUnifiedCompilation.Compiled) (named : Named) (index : Nat) where
  selected : compiled.indexed.base.functions[index]? = some named
  diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)
  found : compiled.indexed.base.diagnostics = some diagnostics
  code : Expr
  cached : compiled.indexed.secondPass.closures[index]? = some code
  compilation : Compilation compiled.indexed named (lowered compiled diagnostics) code
  record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan
    named.signature.key = .ok named.specialized
  functionFirst : Nat
  functionPositive : 0 < functionFirst
  functionIssued : SourceCoreProgramFaultSites.FunctionIssuance functionFirst named.specialized compilation.own
  issued : IssuedSource compiled named.signature.key (source named)
  issuedDiagnostics : issued.diagnostics = diagnostics
  issuedPlan : issued.plan = compiled.indexed.base.plan
  issuedFirst : issued.first = functionFirst + compilation.own.table.reads.length
  assignments : issued.assignments = compilation.own.assignments
  places : PlaceReasonsEq issued.diagnostics.program (lowered compiled diagnostics)

/-- A real selected second-pass action manufactures the first token, inventory
and assignment row internally. No chosen issuer or equality is an input. -/
theorem at_selected {compiled : SourceCoreUnifiedCompilation.Compiled} {named : Named} {index : Nat}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (typing : EmittedDiagnosticTokenPlan.UnaryTyped (source named) ∧
      AssignmentDiagnosticOrigins.OperandsTyped (source named)) :
    Nonempty (SelectedReceipt compiled named index) := by
  obtain ⟨diagnostics, code, found, cached, accepted⟩ := NamedCalls.compiled_at compiled.indexed selected
  obtain ⟨compilation⟩ := CallableIndexedNamedGeneration.of_accepted compiled.indexed accepted
  have record := CallableIndexedActualNamedSourceReceipts.cached_record compiled selected compilation.hook
  obtain ⟨root, extra, prepared⟩ := CallableIndexedOwnedPublicDiagnosticReceipts.compiled_diagnostics compiled found
  have basePrepared := CallableIndexedOwnedPublicDiagnosticReceipts.data_place_base prepared
  have sameBase : (lowered compiled diagnostics).base = diagnostics.program.base := by
    unfold lowered
    cases compiled.indexed.base.callableContext <;> rfl
  have own := compilation.diagnostic
  change (lowered compiled diagnostics).base.find? named.signature.key = some compilation.own at own
  rw [sameBase] at own
  obtain ⟨first, positive, functionIssued⟩ := SourceCoreProgramFaultSites.prepare_function_issuance basePrepared record own
  have assignmentsPrepared : SourceCoreAssignmentFaultSites.prepare (source named)
      (first + compilation.own.table.reads.length) = .ok compilation.own.assignments := by
    cases functionIssued with
    | intro _ _ _ _ assignments _ _ _ _ _ => exact assignments
  let issued : IssuedSource compiled named.signature.key (source named) := {
    first := first + compilation.own.table.reads.length
    assignments := compilation.own.assignments
    assignmentsPrepared := assignmentsPrepared
    typing := typing
    plan := compiled.indexed.base.plan
    root := root
    extra := extra
    diagnostics := diagnostics
    prepared := prepared
    collected := List.mem_append_left _ (selected_collected record) }
  exact ⟨{
    selected := selected
    diagnostics := diagnostics
    found := found
    code := code
    cached := cached
    compilation := compilation
    record := record
    functionFirst := first
    functionPositive := positive
    functionIssued := functionIssued
    issued := issued
    issuedDiagnostics := rfl
    issuedPlan := rfl
    issuedFirst := rfl
    assignments := rfl
    places := placeReasons_of_lowered (compiled := compiled) diagnostics rfl }⟩

/-- The actual method selector supplies diagnostic typing. The old cached slot
and newly retained real slot agree on code; their diagnostic certificates are
not equated or recovered from this equality. -/
theorem at_principal {compiled : SourceCoreUnifiedCompilation.Compiled}
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    ∃ receipt : SelectedReceipt compiled principal.named principal.cached.index,
      receipt.code = principal.cached.code := by
  obtain ⟨receipt⟩ := at_selected principal.cached.selected (SourceDiagnosticTypingOrigins.principal principal wellFormed)
  exact ⟨receipt, Option.some.inj (receipt.cached.symm.trans principal.cached.cached)⟩

/-- A prospective method collector retains this actual compilation and issuer
at formation. The original complete selector and dictionary remain literal. -/
def SelectedReceipt.principal {compiled : SourceCoreUnifiedCompilation.Compiled}
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
    (receipt : SelectedReceipt compiled principal.named principal.cached.index) :
    CallableIndexedOwnedMethodPrincipal.Principal compiled method where
  cached := {
    index := principal.cached.index
    named := principal.named
    diagnostics := lowered compiled receipt.diagnostics
    code := receipt.code
    selected := receipt.selected
    same := principal.cached.same
    cached := receipt.cached
    compilation := receipt.compilation }
  callerContext := principal.callerContext
  callerEvidence := principal.callerEvidence
  traitName := principal.traitName
  methodName := principal.methodName
  requirements := principal.requirements
  dictionary := principal.dictionary
  selected := principal.selected

/-- All Source selector fields are unchanged by positive compiler issuance. -/
theorem SelectedReceipt.principal_source {compiled : SourceCoreUnifiedCompilation.Compiled}
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
    (receipt : SelectedReceipt compiled principal.named principal.cached.index) :
    (SelectedReceipt.principal principal receipt).named = principal.named ∧
      (SelectedReceipt.principal principal receipt).dictionary = principal.dictionary ∧
      (SelectedReceipt.principal principal receipt).sourceBody = principal.sourceBody :=
  ⟨rfl, rfl, rfl⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedDiagnosticIssuerReceipts
