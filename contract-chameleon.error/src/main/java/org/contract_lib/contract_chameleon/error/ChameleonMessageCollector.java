
package org.contract_lib.contract_chameleon.error;

import java.util.List;
import java.util.ArrayList;
import java.util.stream.Stream;

/// Manager for messages that are shown to the user.
public final class ChameleonMessageCollector {

  private final List<ChameleonFileReportable> messages = new ArrayList<>();

  /// Report a new message.
  public void report(ChameleonFileReportable message) {
    messages.add(message);
  }

  /// Get a sorted stream of all messages.
  public Stream<ChameleonFileReportable> getMessages() {
    return messages.stream().sorted();
  }

  /// Write all reported messages to std error.
  public void writeStdErr() {
    messages.stream()
        .map(c -> c.messageType() + c.getMessage())
        .forEachOrdered(System.err::println);
  }

  public ChameleonMessageGroup toMessageGroup(String reason) {
    return new ChameleonMessageGroup(reason, messages);
  }
}
