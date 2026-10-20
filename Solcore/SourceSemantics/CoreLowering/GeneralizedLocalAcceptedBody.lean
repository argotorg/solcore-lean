import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLambdaCompilation
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyFlow

/-! A contextual instance packet already contains its successful body compiler
call. Recover the complete body tree from that call without a lexical scanner
or a restriction on nested declarations, assignments or loops. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedBody
open Core Frontend SourceInference
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet context representation binder policy lowerBody)

def bodyPolicy (inputs : Inputs) (prepared : SourceCoreLocalEvidence.Prepared) (fuel : Nat) :
    SourceCoreLoops.Policy :=
  let repr := representation inputs prepared
  { repr.loopsWithSourceCells repr.expressions.sourceCells
      prepared.caller.function.solvedRequirements inputs.assignments inputs.diagnostics
      inputs.current.owner
      (FunctionCode.children (policy inputs prepared fuel) (lowerBody inputs prepared)
        fuel (context inputs prepared)) with
    sourceCells := repr.expressions.sourceCells
    lowerBinder := binder inputs prepared }

abbrev Receipt {inputs : Inputs} {candidate : SourceCoreLocalPolymorphism.Instance} {raw : Expr}
    (packet : Packet inputs candidate raw) :=
  AcceptedNamedBodyFlow.Body (bodyPolicy inputs packet.original.emission.prepared packet.fuel)
    packet.fuel packet.original.emission.prepared.source packet.certificate.bodyScope
    packet.statements packet.certificate.resultCore inputs.reasonAt
    (context inputs packet.original.emission.prepared).internalReason
    (context inputs packet.original.emission.prepared).internalReason packet.certificate.body

/-- The body belongs to the same contextual candidate, lexical substitution,
parameter scope and exact output stored by its original packet. -/
theorem of_packet {inputs : Inputs} {candidate : SourceCoreLocalPolymorphism.Instance} {raw : Expr}
    (packet : Packet inputs candidate raw) : Nonempty (Receipt packet) := by
  have accepted := packet.certificate.bodyCompiled
  change SourceCoreLoops.lowerStatementsWithPolicy
    (bodyPolicy inputs packet.original.emission.prepared packet.fuel)
    packet.fuel packet.original.emission.prepared.source packet.certificate.bodyScope
    packet.statements packet.certificate.resultCore inputs.reasonAt
    (context inputs packet.original.emission.prepared).internalReason
    (context inputs packet.original.emission.prepared).internalReason = .ok packet.certificate.body at accepted
  exact AcceptedNamedBodyFlow.body_of_accepted accepted

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedBody
