import Solcore.Frontend.Fragments.Local
import Solcore.Frontend.Fragments.RuntimeAdapter
import Solcore.Frontend.Fragments.ClosedSource
import Solcore.Frontend.Fragments.ReturnTree
import Solcore.Frontend.Current

/-!
Compatibility facade for the complete frontend. New whole-program clients may
import `Solcore.Frontend.Current`; historical adapters are grouped under
`Solcore.Frontend.Fragments`.
-/
