import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedHeaderPolicies
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! The actual named matcher checks in its original table and emits exactly
that code under the final frame/marker definitions. Source grammar, independent
source typing and diagnostic interpretation remain separate. Runtime inspection
uses explicit child callbacks; whole callable semantics are covered by existing
regressions, without constructing Header proofs from native comparisons. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedPreparedHeaderPolicies
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open RecursiveNamedCatalog RecursiveNamedPublicSpecializationMeaning
open RecursiveNamedPreparedHeaderPolicies CompatibleMatchAmbientLowering

abbrev actual_static_inputs := @RecursiveNamedPreparedHeaderPolicies.Prepared.inputs
abbrev actual_exact_policy := @RecursiveNamedCatalogRuntimeProfileFactory.Inputs.of_exact
abbrev actual_body_extraction := @GenericImperativeMatch.extraction_of_typed_body_with_lowering

section Actual
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {row : SourceSpecialization.SpecializedFunction}
  (prepared : Prepared compiled row) {instantiation : DeclarationInstantiation}
  {header : Header compiled.indexed.ancestry (.initial compiled.compatible.checked) compiled.indexed.layouts.definitions
    (Program.ofChecked compiled.sourceProgram)}
  (atHeader : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
include atHeader

theorem actual_callback : PolicySuccess header.policy (RecursiveNamedPreparedHeaderPolicies.Prepared.ambientMatch prepared) :=
  RecursiveNamedPreparedHeaderPolicies.Prepared.header_match prepared atHeader

theorem actual_binder (scope : SourceCoreBasic.Scope) (binder : TypedBinder) (closed : binder.scheme.quantified = []) :
    header.policy.lowerBinder header.function.source scope binder =
      SourceCoreCompatibleDataExpressions.lowerBinder compiled.compatible.checked header.function.source scope binder :=
  RecursiveNamedPreparedHeaderPolicies.Prepared.header_binder prepared atHeader scope binder closed

omit atHeader in
theorem actual_tables_differ :
    (RecursiveNamedPreparedHeaderPolicies.Prepared.baseMatch prepared).definitions ≠
      compiled.indexed.layouts.definitions := by
  intro same
  have lengths := congrArg List.length same
  rw [CallableIndexedAmbient.definitions_exact compiled.indexed] at lengths
  simp only [List.length_append, List.length_cons] at lengths
  change compiled.compatible.checked.catalog.definitions.length =
    compiled.compatible.checked.catalog.definitions.length + (_ + 1) at lengths
  omega

omit atHeader in
theorem actual_context_keeps_fields :
    (RecursiveNamedPreparedHeaderPolicies.Prepared.ambientMatch prepared).values =
        (RecursiveNamedPreparedHeaderPolicies.Prepared.baseMatch prepared).values ∧
    (RecursiveNamedPreparedHeaderPolicies.Prepared.ambientMatch prepared).solvedRequirements =
        prepared.named.specialized.function.solvedRequirements ∧
    (RecursiveNamedPreparedHeaderPolicies.Prepared.ambientMatch prepared).sourceCells =
        (RecursiveNamedPreparedHeaderPolicies.Prepared.baseMatch prepared).sourceCells := ⟨rfl, rfl, rfl⟩
end Actual

/-- Only the original empty-context pattern proof is extended. -/
theorem same_pattern {compilation : SourceCoreCompatibleDataMatches.Context} {native : DataEnvironment}
    (extension : compilation.definitions.Extends native)
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreBasic.Scope} {site : StatementId} {span : Syntax.SourceSpan}
    {expected : TypeSystem.Ty} {pattern : TypedMatchPattern} {compiled : SourceCoreCompatibleDataMatches.CertifiedPattern compilation.definitions}
    (accepted : SourceCoreCompatibleDataMatches.compilePattern compilation fuel source scope site span expected pattern = .ok compiled) :
    SourceCoreCompatibleDataMatches.compilePattern (withDefinitions compilation native) fuel source scope site span expected pattern =
      .ok ⟨compiled.pattern, compiled.typed.extend_definitions extension⟩ :=
  compilePattern_success compilation native extension accepted

/-- A valid final-table child need not typecheck in the base table. -/
theorem child_cannot_be_lowered_to_base :
    HasType [.cell (.namedData ⟨0⟩)] (.lambda (.namedData ⟨0⟩) (.namedData ⟨0⟩) (.var 0))
      (.function (.namedData ⟨0⟩) (.namedData ⟨0⟩)) [⟨[.unit]⟩] ∧
    ¬ HasType [.cell (.namedData ⟨0⟩)] (.lambda (.namedData ⟨0⟩) (.namedData ⟨0⟩) (.var 0))
      (.function (.namedData ⟨0⟩) (.namedData ⟨0⟩)) [] := by
  constructor
  · apply infer_sound; decide
  · intro typed
    have inferred := infer_complete typed
    cases inferred

theorem complete_order (compilation : SourceCoreCompatibleDataMatches.Context) (native : DataEnvironment)
    (row : SolvedRequirement) :
    (withDefinitions {compilation with solvedRequirements := row :: row :: compilation.solvedRequirements} native).solvedRequirements =
      row :: row :: compilation.solvedRequirements := rfl

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def content : String := String.intercalate "\n" [
  "enum Choice { Left(Word), Right(Word) }",
  "function tuple(value: (Word, Word)) returns (Word) { match (value) { case (0, x) { return x; } case (x, y) { return x + y; } } }",
  "function choose(value: Word) returns (Word) { match (value) { case 0 { return 3; } default { return 5; } } }",
  "function nominal(value: Choice) returns (Word) { match (value) { case .Left(x) { return x; } case .Right(y) { return y; } } }"
]

/-- Explicit child callbacks isolate the definitions-only compiler bridge.
The allocator, actual source, original scopes and full nominal registry are real. -/
private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let final := compiled.indexed.layouts.definitions
  let base := compiled.compatible.checked.catalog.definitions
  require (base.length < final.length && final.take base.length == base) "ambient definition prefix lost"
  let mut count := 0
  for named in compiled.indexed.base.functions do
    let source := named.specialized.function.typedBody
    let scope := named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))
    let cells := some (CallableIndexedNamedGeneration.allocator compiled.indexed named)
    let original : SourceCoreCompatibleDataMatches.Context :=
      ⟨.initial compiled.compatible.checked, named.specialized.function.solvedRequirements, cells, none⟩
    let ambient := withDefinitions original final
    let nativeContext := SourceCoreLocalCell.coreContext scope ++
      [named.signature.parameterType] ++ compiled.indexed.base.globals.map (·.referenceType) ++
      [.cell compiled.indexed.ancestry.layout.frame.type]
    for node in source.nodes do
      match node with
      | .statement statement => match statement.form with
        | .matchWith resolution =>
          let scrutinee ← match source.lookupExpression? resolution.scrutinee with
            | some node => pure node | none => throw (IO.userError "ambient scrutinee missing")
          let type ← get "actual scrutinee projection" (original.checked.catalog.project scrutinee.type)
          let childExpression : SourceCoreCompatibleDataMatches.ExpressionLowerer := fun _ _ _ _ _ =>
            .ok ⟨type, OptionalCell.read type (.var 0) (Word.ofNatModulo 91)⟩
          let childBody : SourceCoreCompatibleDataMatches.BodyLowerer := fun _ _ _ _ _ _ _ =>
            .ok (LocalLoop.returned (.word (Word.ofNatModulo 73)))
          let code ← get "actual base match" (SourceCoreCompatibleDataMatches.lowerWithReasons original childExpression childBody
            100 source scope statement.id resolution .word (fun _ => Word.ofNatModulo 93) (Word.ofNatModulo 95))
          let lifted ← get "ambient same match" (SourceCoreCompatibleDataMatches.lowerWithReasons ambient childExpression childBody
            100 source scope statement.id resolution .word (fun _ => Word.ofNatModulo 93) (Word.ofNatModulo 95))
          require (code == lifted) "ambient normalization changed ordered whole match code"
          require (infer? nativeContext code final == some (LocalLoop.resultType .word)) "actual child/admin typing lost"
          require (infer? nativeContext code base == none) "base unexpectedly contains actual administrative markers"
          for arm in resolution.cases do
            let before ← get "actual pattern" (SourceCoreCompatibleDataMatches.compilePattern original 100 source
              ((resolution.hiddenScrutinee, type) :: scope) statement.id arm.span scrutinee.type arm.pattern)
            let after ← get "ambient pattern" (SourceCoreCompatibleDataMatches.compilePattern ambient 100 source
              ((resolution.hiddenScrutinee, type) :: scope) statement.id arm.span scrutinee.type arm.pattern)
            require (reprStr before.pattern == reprStr after.pattern) "ambient pattern raw metadata/order changed"
          count := count + 1
        | _ => pure ()
      | _ => pure ()
  require (count == 3) "ambient actual match inventory changed"

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "prepared header ambient policies" content ["tuple", "choose", "nominal"]
  inspect compiled
  IO.println "prepared header policies: actual base/final tables / same ordered match code / ambient children and allocators / default and nominal patterns GREEN"

end Tests.SourceCoreRecursiveNamedPreparedHeaderPolicies
