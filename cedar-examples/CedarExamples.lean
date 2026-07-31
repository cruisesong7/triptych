import Grammars.Decimal
import Generated.Decimal.spec
import Generated.Decimal.parser
import Generated.Decimal.soundness
import Proofs.Decimal.RuleRegistrySoundness
import Grammars.Duration
import Generated.Duration.spec
import Generated.Duration.parser
import Generated.Duration.soundness
import Grammars.Datetime
import Generated.Datetime.spec
import Generated.Datetime.parser
import Generated.Datetime.soundness
import Proofs.Datetime.RuleRegistrySoundness
import Grammars.IPv4
import Generated.IPv4.spec
import Generated.IPv4.parser
import Generated.IPv4.soundness
import Proofs.IPv4.GrammarView
import Grammars.IPv6
import Generated.IPv6.spec
import Generated.IPv6.parser
import Proofs.Datetime.ComponentView

/-!
# Cedar examples

Worked formats, generated artifacts, parser-validation obligations, component views, and
conformance tests. This companion package is intentionally separate from Cedar-free Triptych
core; its Lake manifest owns the optional cedar-lean dependency.
-/
