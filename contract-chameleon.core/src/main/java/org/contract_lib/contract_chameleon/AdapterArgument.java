package org.contract_lib.contract_chameleon;

import java.util.List;

import org.contract_lib.contract_chameleon.error.ChameleonMessageManager;
import org.contract_lib.contract_chameleon.error.InvalidNumberValuesForArgumentsError;

/** A command line argument defines special arguments for adapters.
 * 
 * Every ideally adapters should use the provided default arguments,
 * but are also able to define their own by providing a service for this interface.
 **/
public interface AdapterArgument {

  /** All possible labels, by which the command line arguments can be identified.
   */
  List<String> getLabels();

  /** Help desciption of the CommandLineArgument.
   *
   * This description is automatically added at the end of the help,
   * when an adapters declares that it supports an argument.
   **/
  String getDescription();

  /** The {@ArgumentParser} passes the following values for an argument,
   *  until a new arguemnt is detected.
   *
   * Default implementation checks that the provided list is empty.
   **/
  default void parseArguments(
      String argument,
      ChameleonMessageManager messageManager,
      List<String> providedValues) {
    if (!providedValues.isEmpty()) {
      messageManager.report(new InvalidNumberValuesForArgumentsError(argument, providedValues, 0));
    }
  }
}
