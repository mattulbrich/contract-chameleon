
package org.contract_lib.contract_chameleon.error;

public interface ChameleonReportable  {
  String getLocationIdentifier();
  int getLine();
  int getCharIndex();
  String getMessage();
  String messageType();
}
