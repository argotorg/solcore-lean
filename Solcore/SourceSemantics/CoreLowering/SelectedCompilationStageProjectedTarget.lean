import Solcore.SourceSemantics.Staging.RecursiveProjectedTarget
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPlaceKeyContracts

set_option autoImplicit false
namespace Solcore.SourceSemantics.Staging.Recursive.ProjectedTarget
open Frontend SourceInference Solcore.SourceSemantics.Dynamic
open Solcore.SourceSemantics.CoreLowering

theorem keys_eq_sourceKeys (projections : List PlaceProjection) :
    keys projections = DataPlaceKeyOrder.sourceKeys projections := by
  induction projections with
  | nil => rfl
  | cons projection rest ih =>
      cases projection <;> simp only [keys, DataPlaceKeyOrder.sourceKeys, ih]

theorem Values.to_data {projections : List PlaceProjection} {values : List Dynamic.Value}
    {evaluated : List EvaluatedProjection} (ordered : Values projections values evaluated) :
    DataPlaceKeyOrder.Values projections values evaluated := by
  induction ordered with
  | nil => exact .nil
  | member _ ih => exact .member ih
  | index _ ih => exact .index ih

theorem Values.of_data {projections : List PlaceProjection} {values : List Dynamic.Value}
    {evaluated : List EvaluatedProjection} (ordered : DataPlaceKeyOrder.Values projections values evaluated) :
    Values projections values evaluated := by
  induction ordered with
  | nil => exact .nil
  | member _ ih => exact .member ih
  | index _ ih => exact .index ih

end Solcore.SourceSemantics.Staging.Recursive.ProjectedTarget
