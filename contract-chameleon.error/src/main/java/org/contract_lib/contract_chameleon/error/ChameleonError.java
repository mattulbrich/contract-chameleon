

package org.contract_lib.contract_chameleon.error;

public abstract class ChameleonError implements ChameleonReportable {

  @Override
  public final String messageType() {
    return "ERROR";
  }
} 
