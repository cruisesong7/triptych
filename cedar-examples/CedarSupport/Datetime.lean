module

public import Cedar.Thm.Ext.Datetime
import all Cedar.Thm.Ext.Datetime.Lemmas

namespace CedarSupport.Datetime

public theorem parseComponents_asString
    {components : Cedar.Thm.Datetime.DatetimeComponents}
    (h : components.syntaxWf) :
    Cedar.Thm.Datetime.parseComponents components.asString = some components :=
  Cedar.Thm.Datetime.parseComponents_asString h

end CedarSupport.Datetime
