package org.contract_lib.lang.key.ast;

import java.util.List;

import java.util.function.Function;

public interface KeyFunction {

  <R> R perform(
    Function<UniqueFunction, R> unique,
    Function<DefaultFunction, R> func
  );

  public record UniqueFunction(
    DefaultFunction function
  ) implements KeyFunction {
    @Override
    public <R> R perform(
      Function<UniqueFunction, R> unique,
      Function<DefaultFunction, R> func
    ) {
      return unique.apply(this);
    }
  }

  public record DefaultFunction(
    KeySort returnType,
    String name,
    List<KeySort> parameter
  ) implements KeyFunction {
    @Override
    public <R> R perform(
      Function<UniqueFunction, R> unique,
      Function<DefaultFunction, R> func
    ) {
      return func.apply(this);
    }
  }
}
