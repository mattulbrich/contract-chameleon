package org.contract_lib;

import org.contract_lib.contract_chameleon.cl.ArgumentParser;
import org.contract_lib.contract_chameleon.error.ChameleonMessageManager;

class ContractChameleon {

  public static void main(String[] args) {

    System.err.println(String.format("Available Classpath: %s", System.getProperty("java.class.path")));
    System.err.println(String.format("Current Working Directory: %s", System.getProperty("user.dir")));

    ChameleonMessageManager messageManager = new ChameleonMessageManager();
    ArgumentParser argumentParser = new ArgumentParser();

    argumentParser.parseArguments(args, messageManager);

    argumentParser
        .getAdapter()
        .ifPresent(a -> a.perform(argumentParser, args));

    messageManager.writeStdErr();
  }
}
