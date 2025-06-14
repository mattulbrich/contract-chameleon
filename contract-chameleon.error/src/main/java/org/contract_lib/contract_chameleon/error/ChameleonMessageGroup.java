package org.contract_lib.contract_chameleon.error;

import java.util.List;
import java.util.stream.Collectors;

public final class ChameleonMessageGroup extends Exception {

  List<ChameleonReportable> messages;

  ChameleonMessageGroup(List<ChameleonReportable> messages) {
    this.messages = messages;
  }

  public String getMessage() {
    //TODO: sort messages before printing
    return messages.stream()
      .map(this::messageDescription)
      .collect(Collectors.joining(System.lineSeparator()));
  } 

  public List<ChameleonReportable> getMessages() {
    return messages;
  }

  private String messageDescription(ChameleonReportable message) {
    return String.format(
      "%s in %s: %d|%d -> %s",
      message.messageType(),
      message.getLocationIdentifier(), 
      message.getLine(),
      message.getCharIndex(),
      message.getMessage()
    );
  }
}
