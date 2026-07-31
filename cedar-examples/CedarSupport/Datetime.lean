module

public import Cedar.Thm.Ext.Datetime
import all Cedar.Thm.Ext.Datetime.Lemmas

namespace CedarSupport.Datetime

public theorem parseComponents_asString
    {components : Cedar.Thm.Datetime.DatetimeComponents}
    (h : components.syntaxWf) :
    Cedar.Thm.Datetime.parseComponents components.asString = some components :=
  Cedar.Thm.Datetime.parseComponents_asString h

public theorem computeValue_asString
    {components : Cedar.Thm.Datetime.DatetimeComponents}
    (h : components.syntaxWf) :
    Cedar.Thm.Datetime.computeValue components.asString = some components.toMillis :=
  Cedar.Thm.Datetime.computeValue_asString h

end CedarSupport.Datetime
