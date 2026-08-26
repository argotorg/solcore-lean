import Solcore.Surface.Multi.AuxiliaryLocation
import Solcore.Surface.Multi.CoherentIntervalLocation

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Solcore.Workspace
open Grammar

namespace ActionReduces

/-- Every generated action preserves exact interval evidence.  A list-tail
cons action removes its leading comma only from the semantic roots. -/
theorem auxiliary_locationSound
    {file : WorkspaceFile} {tokens : List Token}
    {production : ProductionId}
    {origin finish : Boundary tokens}
    {input : GrammarSymbolValues file tokens production.rhs}
    {output : NonterminalValue file tokens production.lhs}
    (auxiliary : AuxiliaryProduction production)
    (reduces : ActionReduces file tokens (.actionFor production)
      origin finish input output) :
    ActionLocationSound reduces := by
  intro trace evidence
  have equation := reduces.auxiliary_locationEquation auxiliary
  cases production with
  | root rule => contradiction
  | atom site | seq site | group site | choice site _ | opt site _
      | star site _ | plus site _ | list0 site _ | list1 site =>
      exact IntervalLocationEvidence.replaceFragment equation.symm evidence
  | tail site branch =>
      cases branch with
      | nil =>
          exact IntervalLocationEvidence.replaceFragment equation.symm
            evidence
      | cons =>
          change IntervalLocationEvidence file tokens origin finish
            (NonterminalValue.locationFragment (.tail site) output) trace
          apply IntervalLocationEvidence.dropLeadingRaw
          exact IntervalLocationEvidence.replaceFragment
            (by
              simpa [AuxiliaryActionLocationEquation,
                MatchedTerminal.locationFragment] using equation)
            evidence

end ActionReduces

end Solcore.Surface.Multi

