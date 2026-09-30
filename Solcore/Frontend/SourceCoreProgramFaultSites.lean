import Solcore.Frontend.SourceCoreAssignmentFaultSites
import Solcore.Frontend.SourceCompilationPlan

/-! Program-wide, nonwrapping failure identities. Each specialization keeps its
own read provider; the root entry carries their combined diagnostic table.
This pass only processes source metadata. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreProgramFaultSites

open SourceInference

abbrev Key := SourceSpecialization.SpecializationKey
abbrev Plan := SourceSpecializationWorklist.Plan

structure Function where
  key : Key
  table : SourceCoreFaultSites.Table
  assignments : SourceCoreAssignmentFaultSites.Table
  fellThroughReason : Core.Word
  deriving Repr

structure Program where
  functions : List Function
  rootTable : SourceCoreFaultSites.Table
  deriving Repr

inductive Error where
  | sites (error : SourceCoreFaultSites.Error)
  | assignments (error : SourceCoreAssignmentFaultSites.Error)
  | plan (error : SourceCompilationPlan.Error)
  | invalidFunctionType (key : Key)
  deriving Repr, DecidableEq

private def reason (index : Nat) : Except Error Core.Word :=
  match Core.Word.ofNat? index with
  | some value => pure value
  | none => .error (.sites .reasonSpaceExhausted)

private def collect : Nat → List SourceSpecialization.SpecializedFunction → Except Error (List Function)
  | _, [] => pure []
  | next, specialized :: rest => do
      let sourceResult ← match specialized.function.type with
        | .function _ result => pure result
        | _ => .error (.invalidFunctionType specialized.key)
      let baseSites ← (SourceCoreFaultSites.prepare specialized.function.typedBody sourceResult).mapError Error.sites
      let reads ← baseSites.reads.zipIdx.mapM fun (site, index) => do
        let token ← reason (next + index)
        pure { site with reason := token }
      let assignments ← (SourceCoreAssignmentFaultSites.prepare specialized.function.typedBody
        (next + reads.length)).mapError Error.assignments
      let fellThroughReason ← reason (next + reads.length + assignments.length)
      let escapedReason ← reason (next + reads.length + assignments.length + 1)
      let remaining ← collect (next + reads.length + assignments.length + 2) rest
      let function : Function := {
        key := specialized.key
        table := { baseSites with
          reads := reads
          escapedReason := escapedReason
          additional := assignments.diagnostics }
        assignments
        fellThroughReason := fellThroughReason
      }
      pure (function :: remaining)

def Program.find? (program : Program) (key : Key) : Option Function :=
  program.functions.find? fun function => decide (function.key = key)

/-- Call after canonical plan authentication. Zero remains the root's public
fallthrough token; positive boundary reasons identify the actual callee. -/
def prepare (plan : Plan) (root : Key) : Except Error Program := do
  let functions ← collect 1 plan.specializations
  let selected ← match functions.find? (fun function => decide (function.key = root)) with
    | some function => pure function
    | none => .error (.plan (.missingSpecialization root))
  let reads := functions.flatMap (·.table.reads)
  let additional := functions.flatMap fun function => function.assignments.diagnostics ++ [
    (function.fellThroughReason, {
      error := SourceTypedRuntime.RuntimeError.functionFellThrough function.table.resultType
      site := SourceCoreElaboration.ErrorSite.declaration function.table.owner
      span := none
    }),
    (function.table.escapedReason, {
      error := SourceTypedRuntime.RuntimeError.controlEscapedFunction
      site := SourceCoreElaboration.ErrorSite.declaration function.table.owner
      span := none
    })]
  pure { functions, rootTable := { selected.table with reads, additional } }

end Solcore.Frontend.SourceCoreProgramFaultSites
