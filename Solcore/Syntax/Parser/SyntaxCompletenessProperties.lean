import Solcore.Syntax.Parser.Internal.Completeness
import Solcore.Syntax.Parser.Internal.TermSoundness
import Solcore.Syntax.Parser.Internal.SignatureSoundness
import Solcore.Syntax.Parser.TopItemCompletenessProperties
import Solcore.Syntax.Parser.Internal.SourceFileSoundness
import Solcore.Syntax.Parser.FileItemsCompletenessProperties
import Solcore.Syntax.Parser.PublicParseCompletenessProperties

/-! Public correspondence between independent ordinary syntax and execution.
Success identifies full ASTs and declarative remainders; rejection identifies
its declarative endpoint, not failure payloads or complete parser states. -/
