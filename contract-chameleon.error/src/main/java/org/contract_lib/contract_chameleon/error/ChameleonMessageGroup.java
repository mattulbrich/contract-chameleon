package org.contract_lib.contract_chameleon.error;

import java.util.List;
import java.util.ArrayList;
import java.util.stream.Collectors;

/// A group of messages that have a connection.
public final class ChameleonMessageGroup extends Exception {

  private final List<ChameleonFileReportable> messages;

  /// Create a new message group from a list.
  public ChameleonMessageGroup(List<ChameleonFileReportable> messages) {
    this.messages = new ArrayList<>(messages);
  }

  /// Get a descirption of all messages
  public String getMessage() {
    return messages.stream().sorted()
        .map(ChameleonFileReportable::getMessage)
        .collect(Collectors.joining(System.lineSeparator()));
  }

  /// Get all messages.
  public List<ChameleonFileReportable> getMessages() {
    return new ArrayList<>(this.messages);
  }
}
