package org.contract_lib.contract_chameleon.arguments;

import java.util.List;

import org.contract_lib.contract_chameleon.AdapterArgument;
import org.contract_lib.contract_chameleon.error.ChameleonMessageManager;
import org.contract_lib.contract_chameleon.error.InvalidNumberValuesForArgumentsError;

public final class OutputPath implements AdapterArgument {

  private String path = null;

  public OutputPath() {
  }

  /// All possible labels, by which the command line arguments can be identified
  public List<String> getLabels() {
    return List.of("-o", "--output");
  }

  /// Help desciption of the CommandLineArgument
  public String getDescription() {
    return "Overwrite the directory path of the output.";
  }

  @Override
  public void parseArguments(
      String argument,
      ChameleonMessageManager messageManager,
      List<String> parsedValues) {

    if (parsedValues.size() != 1) {
      messageManager.report(new InvalidNumberValuesForArgumentsError(argument, parsedValues, 1));
      return;
    }
    path = parsedValues.getFirst();
  }

  public String getPath() {
    return path;
  }
}
