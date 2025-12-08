package org.contract_lib.contract_chameleon;

public abstract class Adapter implements AdapterId {
  //TODO: Remove args
  public abstract void perform(
      AdapterArgumentProvider adapterProvider,
      String[] args);
}
