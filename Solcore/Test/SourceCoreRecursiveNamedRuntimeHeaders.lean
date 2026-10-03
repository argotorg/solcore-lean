import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogRuntimeMatchProfiles
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogProfileFactory
import Solcore.Test.SourceCoreRecursiveNamedLexicalRuntimeBounds

/-! Runtime headers use actual source-frame validity without requiring ordinary
validity for every retained row. Legacy profiles retain that stronger premise
explicitly. These checks add no execution model or runtime law to the header. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedRuntimeHeaders
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open RecursiveNamedCatalog GeneralHeap ReadOnly CompatiblePayload CallableAncestryPairedLookup

/-- This complete constructor takes authentic static receipts and independent
program typing; there is no pre-existing Header or ordinary validity input. -/
abbrev actual_from_receipts := @Header.of_source_frame
abbrev runtime_from_receipts := @Header.of_runtime_body

/-- The same actual frame supplies full retained runtime rows and coverage. -/
theorem actual_frame {program : SourceSemantics.Program} {instantiation : DeclarationInstantiation}
    {body : Dynamic.BodyInstance} {function : Dynamic.Closure} {context : SourceSemantics.Context}
    {types : List TypeSystem.Ty} {solved : List SolvedRequirement}
    (frame : NamedCalls.SourceFrame program instantiation body function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (programTyped : ProgramWellFormed program) (sameLedger : function.context.solvedRequirements = solved) :
    CompatibleRuntimeContextValidity.Valid solved context function.evidence :=
  CompatibleRuntimeContextValidity.of_frame frame extended programTyped sameLedger

section Rebuild
variable {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
    {definitions : DataEnvironment} {program : SourceSemantics.Program}

/-- Reconstruct from the same fields without reading the prior validity field.
The public constructor above also works before any Header has been built. -/
private def rebuild (header : Header prepared values definitions program)
    (programTyped : ProgramWellFormed program)
    (sameLedger : header.function.context.solvedRequirements = header.solved) :
    Header prepared values definitions program :=
  Header.of_dictionary_frame
    (function := header.function)
    (instantiation := header.instantiation)
    (sourceBody := header.sourceBody)
    (frame := header.frame)
    (named := header.named)
    (agreement := header.agreement)
    (ordinaryReturn := header.ordinaryReturn)
    (ordinaryParameters := header.ordinaryParameters)
    (target := header.target)
    (context := header.context)
    (types := header.types)
    (bindings := header.bindings)
    (parameters := header.parameters)
    (inputs := header.inputs)
    (extended := header.extended)
    (solved := header.solved)
    (reasonAt := header.reasonAt)
    (readFuel := header.readFuel)
    (output := header.output)
    (policy := header.policy)
    (fuel := header.fuel)
    (fellThrough := header.fellThrough)
    (escaped := header.escaped)
    (body := header.body)
    (parameterCode := header.parameterCode)
    (code := header.code)
    (layouts := header.layouts)
    (owner := header.owner)
    (active := header.active)
    (globals := header.globals)
    (onError := header.onError)
    (acceptedPrefix := header.acceptedPrefix)
    (hook := header.hook)
    (definitions_eq := header.definitions_eq)
    (registered := header.registered)
    (unique := header.unique)
    (parameterType := header.parameterType)
    (resultType := header.resultType)
    (representation := header.representation)
    (compiledFuel := header.compiledFuel)
    (compiled := header.compiled)
    (slot := header.slot)
    (selected := header.selected)
    (cached := header.cached)
    programTyped sameLedger

theorem same_cached_row (header : Header prepared values definitions program)
    (programTyped : ProgramWellFormed program)
    (sameLedger : header.function.context.solvedRequirements = header.solved) :
    (rebuild header programTyped sameLedger).slot = header.slot ∧
      (rebuild header programTyped sameLedger).named = header.named ∧
      (rebuild header programTyped sameLedger).code = header.code ∧
      (rebuild header programTyped sameLedger).compiled = header.compiled :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem same_source (header : Header prepared values definitions program)
    (programTyped : ProgramWellFormed program)
    (sameLedger : header.function.context.solvedRequirements = header.solved) :
    (rebuild header programTyped sameLedger).function = header.function ∧
      (rebuild header programTyped sameLedger).sourceBody = header.sourceBody ∧
      (rebuild header programTyped sameLedger).instantiation = header.instantiation ∧
      (rebuild header programTyped sameLedger).context = header.context :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem same_ordered_inputs (header : Header prepared values definitions program)
    (programTyped : ProgramWellFormed program)
    (sameLedger : header.function.context.solvedRequirements = header.solved) :
    (rebuild header programTyped sameLedger).bindings = header.bindings ∧
      (rebuild header programTyped sameLedger).solved = header.solved := ⟨rfl, rfl⟩

theorem retained_unused_row (header : Header prepared values definitions program)
    (programTyped : ProgramWellFormed program)
    (sameLedger : header.function.context.solvedRequirements = header.solved)
    {row : SolvedRequirement} (member : row ∈ header.solved) :
    row ∈ (rebuild header programTyped sameLedger).context.solvedRequirements := by
  rw [(rebuild header programTyped sameLedger).valid.ledger]
  exact member

theorem old_body_data (body : BuiltinNamedCalls.Body prepared values definitions program) :
    (Header.of_body body).slot = body.slot ∧
      (Header.of_body body).code = body.code ∧
      (Header.of_body body).bindings = body.bindings := ⟨rfl, rfl, rfl⟩

theorem old_body_valid (body : BuiltinNamedCalls.Body prepared values definitions program) :
    (Header.of_body body).valid = CompatibleRuntimeContextValidity.of_ordinary body.valid := rfl
end Rebuild

section LegacyProfiles
variable {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
    {headers : Inventory prepared values ambient.definitions program}
    {header : Header prepared values ambient.definitions program}
    {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat}
    {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {diagnosticPolicy : AssignmentDiagnosticPolicy}

theorem ordinary_profile
    (profile : ProfileFor diagnosticPolicy headers header compilation expressionFuel expressionSyntax administrative registry faults) :
    CompatibleExpressionLiterals.ContextValid header.solved header.context header.function.evidence :=
  profile.initialValid

theorem same_match_condition
    (profile : ProfileFor diagnosticPolicy headers header compilation expressionFuel expressionSyntax administrative registry faults) :
    profile.to_match.initialValid = profile.initialValid := rfl
end LegacyProfiles

/-- Runtime validity of the same full ledger cannot reconstruct the ordinary
condition required by the legacy profile. -/
abbrev runtime_not_ordinary := SourceCoreRecursiveNamedLexicalRuntimeBounds.runtime_not_ordinary

end Tests.SourceCoreRecursiveNamedRuntimeHeaders
