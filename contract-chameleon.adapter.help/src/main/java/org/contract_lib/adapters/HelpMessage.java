
package org.contract_lib.adapters;

import org.contract_lib.contract_chameleon.AdapterId;

public interface HelpMessage extends AdapterId {

  public String adapterDescription();

  public String help();
}
