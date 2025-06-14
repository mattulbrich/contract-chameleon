package org.contract_lib.lang.verifast.ast;

import java.util.List;
import java.util.function.Function;

public record VeriFastFixpoint(
  String name,
  VeriFastType returnType,
  List<VeriFastArgument> arguments,
  VeriFastExpression definition
) implements VeriFastHelper {
  public <R> R perform(
    Function<VeriFastInduction, R> induction,
    Function<VeriFastPredicate, R> predicate,
    Function<VeriFastFixpoint, R> fixpoint 
  ) {
    return fixpoint.apply(this);
  }
}
