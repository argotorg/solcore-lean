import Solcore.SourceSemantics.CoreLowering.CompatibleNamedBodyCompilation
import Solcore.Test.SourceCoreUnifiedCorpusSupport

#check_failure Solcore.SourceSemantics.CoreLowering.CompatibleNamedBody.Certificate.mk
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Static zero-parameter compilation receipts and concrete checked source
regressions. Semantic certificates are extracted at one actual body context;
neither a universal body IH nor a finite source execution is a static premise. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleNamedBody
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleNamedBody

private def source (owner : Resolved.DeclarationId) : TypedSource := {
  owner, inputs := [], roots := [], nodes := [] }
private def compilation (plan : SourceSpecializationWorklist.Plan)
    (owner : SourceSpecialization.SpecializationKey) : SourceCoreFunctions.Context := {
  plan, owner, globals := [], administrativePrefix := 1, solvedRequirements := [], internalReason := Word.zero }
private def policy (program : CheckedProgram) (representation : SourceCoreGeneralFunctions.Representation)
    (plan : SourceSpecializationWorklist.Plan) (owner : SourceSpecialization.SpecializationKey)
    (values : SourceCoreCompatibleValues.Context)
    (assignments : SourceCoreAssignmentFaultSites.Table) (diagnostics : SourceCoreDataPlaceFaultSites.Program) :
    SourceCoreLoops.Policy := {
  lowerExpression := SourceCoreGeneralFunctions.lowerContextualExpression program representation program.signatures
    ⟨[]⟩ [] assignments diagnostics (compilation plan owner) none none none
  readStatement := SourceCoreCompatibleDataExpressions.readStatement values.checked
}
private def code (fellThrough escaped : Word) : Expr :=
  CompatibleStatements.finish .unit (LocalLoop.fallthrough .unit) fellThrough escaped

/-- Even the empty body uses the actual contextual compiler and explicit
source context. No `BodyPreserves` or `BodyReflects` premise is hidden here. -/
theorem nil_certificate (program : CheckedProgram) (representation : SourceCoreGeneralFunctions.Representation)
    (plan : SourceSpecializationWorklist.Plan) (owner : SourceSpecialization.SpecializationKey)
    (readFuel : Nat) (values : SourceCoreCompatibleValues.Context)
    (assignments : SourceCoreAssignmentFaultSites.Table) (diagnostics : SourceCoreDataPlaceFaultSites.Program)
    (context : SourceSemantics.Context) (fellThrough escaped : Word)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (readExpression : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerRead : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafLowerer : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values) :
    Nonempty (Certificate readFuel values (source owner.declaration) context [] (fun _ => Word.zero) [] [] .unit .unit
      (policy program representation plan owner values assignments diagnostics) 10 fellThrough escaped (code fellThrough escaped)) := by
  apply of_contextual (locals := ⟨[]⟩) (compilation := compilation plan owner)
      (native := none) (parent := none) (skipInitializer := none) ?_ ?_ closed residual ?_
      readExpression lowerRead leafLowerer rfl rfl .nil rfl rfl
  · constructor
    · intro id node _ found
      change none = some node at found; cases found
    · intro id node _ found
      change none = some node at found; cases found
    · intros; rfl
    · intros; rfl
  · cbv; decide
  · intro binder declared index native selected accepted
    cases selected

example (environment : Environment) (store : Store) (fellThrough escaped : Word) :
    Evaluates environment store (code fellThrough escaped) (.inRight .word .unit) store := by
  exact LocalControl.finish_fallthrough .unit
    (LocalLoop.toControl_normal .unit escaped (LocalLoop.fallthrough_evaluates .unit environment store))
    (by simpa [LanguageResult.success, Expr.weakenAt] using
      (show Evaluates (.unit :: .inLeft .unit .unit :: environment) store (.inRight .word .unit)
        (.inRight .word .unit) store from .inRight .unit))

private def content : String := String.intercalate "\n" [
  "function empty() { }",
  "function explicitUnit() { return; }",
  "function falseValue() returns (Bool) { return false; }",
  "function pair() returns ((Word, Bool)) { return (7, false); }",
  "function discardReturn() returns (Word) { false; return 9; }",
  "function early() returns (Word) { return 11; 99; }"
]

/-- Concrete named invocation uses the actual cached indexed compiler, with
opaque initial source cells and genuine native suspension/resumption. These
runtime regressions do not replace the independent semantic proofs above. -/
def run : IO Unit := do
  let names := ["empty", "explicitUnit", "falseValue", "pair", "discardReturn", "early"]
  let artifact ← SourceCoreUnifiedCorpusSupport.prepare "certified ordinary named bodies" content names
  let expected : List SourceTypedRuntime.Value := [.unit, .unit, .bool false,
    .product (.word (Word.ofNatModulo 7)) (.bool false), .word (Word.ofNatModulo 9), .word (Word.ofNatModulo 11)]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩]}
  for (name, value) in names.zip expected do
    for fuel in [0, 13, 300000] do
      let first ← SourceCoreUnifiedCorpusSupport.execute artifact name [] fuel initial
      let result ← SourceCoreUnifiedCorpusSupport.get "named body resume" (SourceCoreUnifiedCompilation.Result.resume first 300000)
      match result.observation with
      | .done actual final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr value) s!"named result changed {name}"
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr final.heap == reprStr initial.heap) s!"zero-parameter body changed heap {name}"
      | other => throw (IO.userError s!"named body failed {name}: {reprStr other}")
  IO.println "compatible zero-parameter named bodies, real Core resume and inert source prefix GREEN"

end Tests.SourceCoreCompatibleNamedBody
