package org.contract_lib.lang.verifast.ast;

import java.util.function.Function;

public interface VeriFastHelper {
  <R> R perform(
    Function<VeriFastInduction, R> induction,
    Function<VeriFastPredicate, R> predicate,
    Function<VeriFastFixpoint, R> fixpoint 
  );
}
