package org.contract_lib.contract_chameleon.error;

import java.util.Optional;

public interface ChameleonReportable {
  /// One line desciption of the message.
  String getMessage();

  /// Detailed desciption of the message.
  Optional<String> getDetailedMessage();

  /// The type of the message.
  ChameleonMessageType messageType();

}
