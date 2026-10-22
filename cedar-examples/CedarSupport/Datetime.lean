module

public import Cedar.Thm.Ext.Datetime
import all Cedar.Thm.Ext.Datetime.Lemmas

namespace CedarSupport.Datetime

public theorem toMillis_int64_range
    {components : Cedar.Thm.Datetime.DatetimeComponents}
    (hsyntax : components.syntaxWf) (hconstraints : components.constraintsWf) :
    Int64.MIN ≤ components.toMillis ∧ components.toMillis ≤ Int64.MAX :=
  Cedar.Thm.Datetime.toMillis_int64_range hsyntax hconstraints

end CedarSupport.Datetime
