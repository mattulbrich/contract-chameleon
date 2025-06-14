package org.contract_lib;

import org.contract_lib.contract_chameleon.Adapter;
import org.contract_lib.contract_chameleon.AdapterMap;

class ContractChameleon {

  public static void main(String[] args) {

    String classpath = System.getProperty("java.class.path");
    System.err.println("Classpath: " + classpath);

    Adapter adapter = getAdapter(args);

    if (adapter == null) {
      System.err.println("Adapter not found!");
      return;
    }

    adapter.perform(args);
  }

  private static final String DEAFULT_ADAPTER_NAME = "help";

  public static Adapter getAdapter(String[] args) {
    AdapterMap<Adapter> adapterMap = new AdapterMap<Adapter>(Adapter.class);

    if (args.length < 1) {
      System.err.println("No adapter selected!");
      return adapterMap.get(DEAFULT_ADAPTER_NAME);
    }

    System.err.println("User Dir:" + System.getProperty("user.dir"));

    String adapterName = args[0];

    return adapterMap.get(adapterName);
  }
}
