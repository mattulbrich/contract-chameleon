package org.contract_lib.contract_chameleon.error;

import java.util.Comparator;
import java.util.Optional;

public abstract class ChameleonFileReportable implements Comparable<ChameleonFileReportable>, ChameleonReportable {

  /// Interface for messages of contract-chameleon.
  /// The location (file path) where the message appears.
  abstract String getLocationIdentifier();

  /// The line where the message appears.
  abstract int getLine();

  /// The index in the line where the message appears.
  abstract int getCharIndex();

  public final String getMessage() {
    return String.format(
        "%s in %s: %d|%d -> %s",
        this.messageType(),
        this.getLocationIdentifier(),
        this.getLine(),
        this.getCharIndex(),
        this.getMessage());
  }

  /// Detailed desciption of the message.
  public abstract Optional<String> getDetailedMessage();

  /// The type of the message.
  public abstract ChameleonMessageType messageType();;

  public int compareTo(ChameleonFileReportable o) {
    return Comparator.comparing(ChameleonFileReportable::getLocationIdentifier)
        .thenComparing(ChameleonFileReportable::getLine)
        .thenComparing(ChameleonFileReportable::getCharIndex)
        .thenComparing(ChameleonFileReportable::messageType)
        .compare(this, o);
  }
}
