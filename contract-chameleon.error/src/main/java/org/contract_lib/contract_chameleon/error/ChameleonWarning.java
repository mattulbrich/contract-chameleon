
package org.contract_lib.contract_chameleon.error;

public abstract class ChameleonWarning implements ChameleonReportable {
  @Override
  public final String messageType() {
    return "WARNING";
  }
} 
