package org.contract_lib.lang.verifast.ast;

import java.util.List;
import java.util.function.Function;

public record VeriFastInduction(
  String name,
  List<VeriFastInductionConstructor> constructors
) implements VeriFastHelper {
  public <R> R perform(
    Function<VeriFastInduction, R> induction,
    Function<VeriFastPredicate, R> predicate,
    Function<VeriFastFixpoint, R> fixpoint 
  ) {
    return induction.apply(this);
  }
}
