package org.contract_lib.contract_chameleon.error;

import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

/// Error case when there are labels for an argument but none are expected.
public final class InvalidNumberValuesForArgumentsError implements ChameleonReportable {

  private static final String ARGUMENT_SEPARATOR = " ";

  private String argument;
  private List<String> valuesProvided;
  private int numberValuesExpected;

  public InvalidNumberValuesForArgumentsError(
      String argument,
      List<String> valuesProvided,
      int numberValuesExpected) {
    this.argument = argument;
    this.valuesProvided = valuesProvided;
    this.numberValuesExpected = numberValuesExpected;
  }

  @Override
  public String getMessage() {
    return String.format("The argument '%s' expectes %d values, provided with: '%s'",
        argument,
        numberValuesExpected,
        valuesProvided.stream().collect(Collectors.joining(ARGUMENT_SEPARATOR)));
  }

  @Override
  public ChameleonMessageType messageType() {
    return ChameleonMessageType.ERROR;
  }

  @Override
  public Optional<String> getDetailedMessage() {
    return Optional.empty();
  }
}
