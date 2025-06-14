package org.contract_lib.lang.verifast.ast;

import java.util.List;
import java.util.Optional;
import java.util.function.Function;

public interface VeriFastExpression {

  <R> R perform(
      Function<Chain, R> chain,
      Function<BooleanValue, R> boolV,
      Function<IntegerValue, R> intV,
      Function<Predicate, R> pred,
      Function<Variable, R> var,
      Function<VariableAssignment, R> varAss,
      Function<BinaryOperation, R> binOp,
      Function<Fixpoint, R> fixpoint
  );

  public record Chain(
      List<VeriFastExpression> expressions
  ) implements VeriFastExpression {

    @Override
    public <R> R perform(
        Function<Chain, R> chain,
        Function<BooleanValue, R> boolV,
        Function<IntegerValue, R> intV,
        Function<Predicate, R> pred,
        Function<Variable, R> var,
        Function<VariableAssignment, R> varAss,
        Function<BinaryOperation, R> binOp,
        Function<Fixpoint, R> fixpoint
    ) {
      return chain.apply(this);
    }
  }

  public record BooleanValue(
      boolean value) implements VeriFastExpression {

    @Override
    public <R> R perform(
      Function<Chain, R> chain,
      Function<BooleanValue, R> boolV,
      Function<IntegerValue, R> intV,
      Function<Predicate, R> pred,
      Function<Variable, R> var,
      Function<VariableAssignment, R> varAss,
      Function<BinaryOperation, R> binOp,
      Function<Fixpoint, R> fixpoint
    ) {
      return boolV.apply(this);
    }
  }

  public record IntegerValue(
      String value) implements VeriFastExpression {

    @Override
    public <R> R perform(
      Function<Chain, R> chain,
      Function<BooleanValue, R> boolV,
      Function<IntegerValue, R> intV,
      Function<Predicate, R> pred,
      Function<Variable, R> var,
      Function<VariableAssignment, R> varAss,
      Function<BinaryOperation, R> binOp,
      Function<Fixpoint, R> fixpoint
    ) {
      return intV.apply(this);
    }
  }

  public record Predicate(
      Optional<VeriFastExpression.Variable> owner,
      String predicateName,
      List<VeriFastExpression> arguments) implements VeriFastExpression {

    @Override
    public <R> R perform(
      Function<Chain, R> chain,
      Function<BooleanValue, R> boolV,
      Function<IntegerValue, R> intV,
      Function<Predicate, R> pred,
      Function<Variable, R> var,
      Function<VariableAssignment, R> varAss,
      Function<BinaryOperation, R> binOp,
      Function<Fixpoint, R> fixpoint
    ) {
      return pred.apply(this);
    }
  }

  public record Variable(
      String variable) implements VeriFastExpression {

    @Override
    public <R> R perform(
      Function<Chain, R> chain,
      Function<BooleanValue, R> boolV,
      Function<IntegerValue, R> intV,
      Function<Predicate, R> pred,
      Function<Variable, R> var,
      Function<VariableAssignment, R> varAss,
      Function<BinaryOperation, R> binOp,
      Function<Fixpoint, R> fixpoint
    ) {
      return var.apply(this);
    }
  }

  public record VariableAssignment(
      String variable) implements VeriFastExpression {

    @Override
    public <R> R perform(
      Function<Chain, R> chain,
      Function<BooleanValue, R> boolV,
      Function<IntegerValue, R> intV,
      Function<Predicate, R> pred,
      Function<Variable, R> var,
      Function<VariableAssignment, R> varAss,
      Function<BinaryOperation, R> binOp,
      Function<Fixpoint, R> fixpoint
    ) {
      return varAss.apply(this);
    }
  }

  public record BinaryOperation(
      String operation,
      VeriFastExpression left,
      VeriFastExpression right
  ) implements VeriFastExpression {

    @Override
    public <R> R perform(
      Function<Chain, R> chain,
      Function<BooleanValue, R> boolV,
      Function<IntegerValue, R> intV,
      Function<Predicate, R> pred,
      Function<Variable, R> var,
      Function<VariableAssignment, R> varAss,
      Function<BinaryOperation, R> binOp,
      Function<Fixpoint, R> fixpoint
    ) {
      return binOp.apply(this);
    }
  }

  public record Fixpoint(
      String operation,
      List<VeriFastExpression> parameters
  ) implements VeriFastExpression {

    @Override
    public <R> R perform(
      Function<Chain, R> chain,
      Function<BooleanValue, R> boolV,
      Function<IntegerValue, R> intV,
      Function<Predicate, R> pred,
      Function<Variable, R> var,
      Function<VariableAssignment, R> varAss,
      Function<BinaryOperation, R> binOp,
      Function<Fixpoint, R> fixpoint
    ) {
      return fixpoint.apply(this);
    }
  }
}
