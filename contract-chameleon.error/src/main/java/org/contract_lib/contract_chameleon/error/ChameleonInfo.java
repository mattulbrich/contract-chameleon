
package org.contract_lib.contract_chameleon.error;

public abstract class ChameleonInfo implements ChameleonReportable {
  @Override
  public final String messageType() {
    return "INFO";
  }
} 
