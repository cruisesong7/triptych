import Decimal.grammar
import Decimal.spec
import Decimal.parser
import Decimal.soundness
import Decimal.RuleRegistrySoundness
import Duration.grammar
import Duration.spec
import Duration.parser
import Duration.soundness
import Datetime.grammar
import Datetime.spec
import Datetime.parser
import Datetime.soundness
import IPv4.grammar
import IPv4.spec
import IPv4.parser
import IPv4.CedarBridge
import IPv6.grammar
import IPv6.spec
import IPv6.parser
import Duration.CedarBridge
import Datetime.CedarBridge

/-!
# Cedar examples

Worked formats, generated artifacts, parser-validation obligations, Cedar bridge proofs, and
conformance tests. This companion package is intentionally separate from Cedar-free Triptych
core; its Lake manifest owns the optional cedar-lean dependency.
-/
