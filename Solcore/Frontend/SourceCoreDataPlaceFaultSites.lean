import Solcore.Frontend.SourceCoreDataPlaces
import Solcore.Frontend.SourceCoreDataFaultSites

/-! Exact assignment-site diagnostics for absent projected roots and missing
mapping defaults. Header items share their owning for statement's span. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreDataPlaceFaultSites

open SourceInference
abbrev Key := SourceSpecialization.SpecializationKey
abbrev Plan := SourceSpecializationWorklist.Plan

structure Site where
  owner : Key
  location : SourceCoreElaboration.ErrorSite
  binder : Resolved.LocalId
  missingType : Option TypeSystem.Ty
  reason : Core.Word
  diagnostic : SourceCoreFaultSites.Diagnostic
  deriving Repr, DecidableEq

structure Program where
  base : SourceCoreProgramFaultSites.Program
  expressions : SourceCoreDataFaultSites.Program
  places : List Site
  rootTable : SourceCoreFaultSites.Table
  deriving Repr

inductive Error where
  | base (error : SourceCoreDataFaultSites.Error)
  | lowering (error : SourceCoreBasic.Error)
  | reasonSpaceExhausted
  deriving Repr, DecidableEq

private def add (start : Nat) (owner : Key) (location : SourceCoreElaboration.ErrorSite)
    (span : Syntax.SourceSpan) (binder : Resolved.LocalId) (missingType : Option TypeSystem.Ty)
    (sites : List Site) : Except Error (List Site) := do
  if sites.any (fun site => decide (site.owner = owner ∧ site.location = location ∧
      site.binder = binder ∧ site.missingType = missingType)) then return sites
  let reason ← match Core.Word.ofNat? (start + sites.length) with
    | some reason => pure reason
    | none => throw .reasonSpaceExhausted
  let diagnostic : SourceCoreFaultSites.Diagnostic := {
    error := match missingType with
      | none => .invalidPlaceProjection
      | some type => .typeMismatch type none
    site := location, span := some span
  }
  pure (sites ++ [⟨owner, location, binder, missingType, reason, diagnostic⟩])

private def targets (node : StatementNode) : List AssignmentResolution :=
  match node.form with
  | .assignValue assignment _ _ | .assignBitNot assignment => [assignment]
  | .forLoop initial _ post _ => (initial ++ post).filterMap fun
      | .assignValue assignment _ _ | .assignBitNot assignment => some assignment
      | _ => none
  | _ => []

def prepare (checked : SourceCoreDataCatalog.Checked) (signatures : ProgramSignatures)
    (plan : Plan) (root : Key) : Except Error Program := do
  let expressions ← (SourceCoreDataFaultSites.prepare plan root).mapError Error.base
  let used := expressions.rootTable.reads.map (·.reason.val) ++
    expressions.rootTable.additional.map (·.1.val) ++ [expressions.rootTable.escapedReason.val]
  let start := used.foldl max 0 + 1
  let mut places := []
  for specialized in plan.specializations do
    let source := specialized.function.typedBody
    for node in source.nodes do
      match node with
      | .statement node =>
          let site := SourceCoreElaboration.ErrorSite.occurrence node.id.occurrence
          for assignment in targets node do
            let route ← (SourceCoreDataPlaces.describe checked signatures source site assignment).mapError Error.lowering
            unless route.steps.isEmpty do
              places ← add start specialized.key site node.span assignment.target.root none places
            for step in route.steps do
              match step with
              | .index _ _ valueType =>
                  places ← add start specialized.key site node.span assignment.target.root (some valueType) places
              | _ => pure ()
      | _ => pure ()
  let rootTable := { expressions.rootTable with
    additional := expressions.rootTable.additional ++ places.map (fun site => (site.reason, site.diagnostic)) }
  pure ⟨expressions.base, expressions, places, rootTable⟩

def Program.reasonAt (program : Program) (owner : Key) (id : ExpressionId) : Core.Word :=
  program.expressions.reasonAt owner id

def Program.placeReason (program : Program) (owner : Key) (site : SourceCoreElaboration.ErrorSite)
    (binder : Resolved.LocalId) (missingType : Option TypeSystem.Ty) : Core.Word :=
  match program.places.find? (fun candidate => decide (candidate.owner = owner ∧ candidate.location = site ∧
      candidate.binder = binder ∧ candidate.missingType = missingType)) with
  | some candidate => candidate.reason
  | none => Core.Word.zero

end Solcore.Frontend.SourceCoreDataPlaceFaultSites
