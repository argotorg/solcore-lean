import Solcore.SourceSemantics.Staging.RecursiveScope

/-! Bare targets retain their cell before the right-hand expression runs.
This receipt has no expression evaluator: an empty projection path only looks
up the lexical reference and reads its current optional value. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.Staging.Recursive
open Frontend Frontend.SourceInference Solcore.SourceSemantics.Dynamic

inductive BareTarget (environment : Environment) (heap : Heap)
    (place : PlaceResolution) : ResolvedPlace → Prop where
  | intro {location cell initial}
      (bare : place.projections = [])
      (lookup : Environment.LooksUp environment place.root location)
      (read : Heap.Reads heap location cell)
      (value : RootInitialValue cell initial) :
      BareTarget environment heap place
        { location := location, rootType := cell.type, valueType := place.type,
          projections := [], selected := initial }

namespace BareTarget

theorem resolves {environment : Environment} {heap : Heap}
    {place : PlaceResolution} {target : ResolvedPlace}
    (snapshot : BareTarget environment heap place target)
    (program : Program) (context : Context) (evidence : EvidenceEnvironment)
    (source : TypedSource) :
    SourcePlaceResolves program context evidence source environment heap place target heap := by
  cases snapshot with
  | intro bare lookup read value =>
      exact .intro lookup read (bare ▸ .nil) read value .nil

theorem of_resolves {program : Program} {context : Context}
    {evidence : EvidenceEnvironment} {source : TypedSource}
    {environment : Environment} {before after : Heap}
    {place : PlaceResolution} {target : ResolvedPlace}
    (bare : place.projections = [])
    (resolved : SourcePlaceResolves program context evidence source environment before place target after) :
    before = after ∧ BareTarget environment before place target := by
  cases resolved with
  | intro lookup initialRead evaluate currentRead initial selection =>
      rw [bare] at evaluate
      cases evaluate
      cases selection
      exact ⟨rfl, .intro bare lookup currentRead initial⟩

end BareTarget
end Solcore.SourceSemantics.Staging.Recursive
