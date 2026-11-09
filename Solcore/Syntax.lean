import Solcore.Syntax.Declaration
import Solcore.Syntax.Validity
import Solcore.Syntax.Internal.TypeOutcomes
import Solcore.Syntax.Grammar.SourceFile
import Solcore.Syntax.Grammar.Basics
import Solcore.Syntax.Internal.DelimitedExactness
import Solcore.Syntax.Internal.DelimitedOutcomes
import Solcore.Syntax.Lexer
import Solcore.Syntax.Identifier
import Solcore.Syntax.Parser
import Solcore.Syntax.Parser.Correctness
import Solcore.Syntax.Parser.Internal.ExportSoundness
import Solcore.Syntax.Parser.Internal.ContractBodySoundness
import Solcore.Syntax.Parser.Internal.ContractProofs
import Solcore.Syntax.Parser.Internal.ContractOutcomeSoundness
import Solcore.Syntax.Parser.Internal.ContractEntryProofs
import Solcore.Syntax.Parser.Internal.TermSoundness
import Solcore.Syntax.Parser.Internal.SignatureSoundness
import Solcore.Syntax.Parser.Internal.DelimitedSoundness
import Solcore.Syntax.Parser.Internal.DeriveSoundness
import Solcore.Syntax.Parser.Internal.EnumProofs
import Solcore.Syntax.Parser.Internal.ExportProofs
import Solcore.Syntax.Parser.Internal.FileProofs
import Solcore.Syntax.Parser.Internal.ImplProofs
import Solcore.Syntax.Parser.Internal.ParameterSoundness
import Solcore.Syntax.Parser.Internal.ImportSoundness
import Solcore.Syntax.Parser.Internal.ImportProofs
import Solcore.Syntax.Parser.Internal.ParseProperties
import Solcore.Syntax.Parser.PublicOutputs
import Solcore.Syntax.Parser.Internal.TypeSoundness
import Solcore.Syntax.Parser.Internal.SourceFileSoundness
import Solcore.Syntax.Parser.Internal.TraceSummary
import Solcore.Syntax.Parser.Internal.TraitProofs
import Solcore.Syntax.Parser.Internal.TypeAliasProofs
import Solcore.Syntax.Parser.Internal.YulPublicSoundness
import Solcore.Syntax.Parser.Internal.TriviaProofs
import Solcore.Syntax.Parser.Internal.Basics
import Solcore.Syntax.Parser.State
import Solcore.Syntax.Parser.Internal.YulExpressionSoundness

/-!
# Syntax

The AST, the lexer, the parser, and the proofs that the parser matches an independent grammar.
Read in this order. `docs/guide/syntax.md` lists every file.

1. **AST.** `Source`, `Token`, `Foundation`, `Type`, `Term`, `Yul`, `Declaration`, `Module` and
   `Trivia`.
2. **Lexer.** `Lexer/Core` defines `lex`, `Lexer/Contract` states what its output satisfies, and
   `Lexer/Properties` proves it.
3. **Parser.** `Parser` defines `parse` and `parseLexed`. The productions are, in dependency order,
   in `Parser/Tokens`, `Parser/Types`, `Parser/Signatures`, `Parser/Blocks`, `Parser/Yul`,
   `Parser/Terms`, `Parser/Declarations`, `Parser/Modules` and `Parser/SourceFiles`.
4. **Grammar.** `Grammar/` is the specification: which tokens derive which AST, with no reference
   to the parser. Start at `PublicSourceFileOrdinaryParses` in `Grammar/SourceFile`. `Validity`
   states when a tree's spans belong to a file.
5. **Main theorems.** `Parser/Correctness` proves that `parse` is total, sound and complete against
   the grammar, that the AST is unique, and that its spans belong to the file.
   `Parser/PublicOutputs` fixes the whole output on complete slices of the language.

`Internal/` holds the grammar-level proofs and `Parser/Internal/` the parser-level proofs.
-/
