import Solcore.SourceSemantics.Staging.RecursiveProjectedTarget
import Solcore.SourceSemantics.Dynamic.Typing

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.Staging.Recursive.ProjectedTarget
open Frontend SourceInference Solcore.SourceSemantics.Dynamic

theorem RootFault.excluded {context : Context} {environment : Environment} {heap : Heap}
    {place : PlaceResolution} {root : TypeSystem.Ty} {reason : SemanticFault}
    (failed : RootFault environment heap place reason)
    (writable : WritableLocal context place.root root)
    (locals : EnvironmentAgrees heap context.locals environment) : False := by
  obtain ⟨scheme, declared, _wellFormed, _mono, _body⟩ := writable.scheme
  obtain ⟨location, cell, lookup, read, _type, _storage⟩ := locals.lookup declared
  cases failed with
  | unbound missing => exact missing.excludes_lookup lookup
  | dangling present missing =>
      cases present.functional lookup
      exact missing.excludes_read read

end Solcore.SourceSemantics.Staging.Recursive.ProjectedTarget
