package org.contract_lib.contract_chameleon.error;

import java.util.List;
import java.util.Optional;
import java.util.ArrayList;
import java.util.Comparator;

/** A group of messages that have a connection.
 *
 * If there are multiple reasons,
 * why an operation cannot be 
 **/
public final class ChameleonMessageGroup implements ChameleonReportable {

  private final List<ChameleonFileReportable> messages;
  private final String message;

  /// Create a new message group from a list.
  public ChameleonMessageGroup(String message, List<ChameleonFileReportable> messages) {
    this.messages = new ArrayList<>(messages);
    this.message = message;
  }

  @Override
  public Optional<String> getDetailedMessage() {

    StringBuilder builder = new StringBuilder(message);
    builder.append(System.lineSeparator());
    messages.stream().sorted()
        .forEachOrdered(c -> {
          builder.append(c.messageType());
          builder.append(": ");
          builder.append(c.getMessage());
          builder.append(System.lineSeparator());
          c.getDetailedMessage().ifPresent(d -> printDetailedMessage(builder, d));
        });
    return Optional.of(builder.toString());
  }

  private void printDetailedMessage(StringBuilder builder, String detailedMessage) {
    //TODO: Printing and formatting of detailed messages
  }

  /// Returns the heighest message type.
  /// If there is no message, {@ChameleonMessageType#ERROR} is returned. 
  @Override
  public ChameleonMessageType messageType() {
    return messages.stream()
        .max(Comparator.comparing(ChameleonFileReportable::messageType))
        .map(ChameleonFileReportable::messageType)
        .orElseGet(() -> ChameleonMessageType.ERROR);
  }

  /// Get a descirption of all messages
  @Override
  public String getMessage() {
    StringBuilder builder = new StringBuilder(message);
    builder.append(System.lineSeparator());
    messages.stream().sorted()
        .forEachOrdered(c -> {
          builder.append(c.messageType());
          builder.append(": ");
          builder.append(c.getMessage());
          builder.append(System.lineSeparator());
        });
    return builder.toString();
  }

  /// Get all messages.
  public List<ChameleonFileReportable> getMessages() {
    return new ArrayList<>(this.messages);
  }
}
