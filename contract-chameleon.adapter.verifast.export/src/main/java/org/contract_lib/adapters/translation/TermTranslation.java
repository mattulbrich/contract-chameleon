package org.contract_lib.adapters.translation;

import java.util.List;

import org.contract_lib.lang.contract_lib.ast.Sort;
import org.contract_lib.lang.contract_lib.ast.Term;

import org.contract_lib.lang.verifast.ast.VeriFastExpression;
import org.contract_lib.lang.verifast.ast.VeriFastType;

public interface TermTranslation {

  Term.Identifier.IdentifierValue getClibIdentifier();

  VeriFastExpression getVerifastTerm(List<VeriFastExpression> parameters);

  List<Sort> getClibParameterTypes();

  List<VeriFastType> getVerifastParameterTypes();

  Sort getClibResultType();

  VeriFastType getVerifastResultType();

  public record ConstantTranslation(
      Term.Identifier.IdentifierValue verifastIdentifier,
      String operation,
      Sort clibResultType,
      VeriFastType verifastResultType) implements TermTranslation {

    public Term.Identifier.IdentifierValue getClibIdentifier() {
      return this.verifastIdentifier;
    }

    public VeriFastExpression getVerifastTerm(List<VeriFastExpression> parameters) {
      if (parameters.size() != 0) {
        //TODO: prop. error handling
        System.err.println("Unexpected number of arguments for constant translation");
      }
      return new VeriFastExpression.Variable(operation);
    }

    public List<Sort> getClibParameterTypes() {
      return List.of();
    }

    public List<VeriFastType> getVerifastParameterTypes() {
      return List.of();
    }

    public Sort getClibResultType() {
      return this.clibResultType;
    }

    public VeriFastType getVerifastResultType() {
      return this.verifastResultType;
    }
  }

  public record UnaryOperatorTranslation(
      Term.Identifier.IdentifierValue verifastIdentifier,
      String operation,
      Sort clibParameterTypes,
      VeriFastType verifastParameterTypes,
      Sort clibResultType,
      VeriFastType verifastResultType) implements TermTranslation {

    public Term.Identifier.IdentifierValue getClibIdentifier() {
      return this.verifastIdentifier;
    }

    public VeriFastExpression getVerifastTerm(List<VeriFastExpression> parameters) {
      if (parameters.size() != 1) {
        //TODO: prop. error handling
        System.err.println("Unexpected number of arguments for unary operator");
      }
      return new VeriFastExpression.Fixpoint(operation, parameters);
    }

    public List<Sort> getClibParameterTypes() {
      return List.of(this.clibParameterTypes);
    }

    public List<VeriFastType> getVerifastParameterTypes() {
      return List.of(this.verifastParameterTypes);
    }

    public Sort getClibResultType() {
      return this.clibResultType;
    }

    public VeriFastType getVerifastResultType() {
      return this.verifastResultType;
    }
  }

  public record BinaryOperatorTranslation(
      Term.Identifier.IdentifierValue verifastIdentifier,
      String operation,
      Sort clibParameterTypes,
      VeriFastType verifastParameterTypes,
      Sort clibResultType,
      VeriFastType verifastResultType) implements TermTranslation {

    public Term.Identifier.IdentifierValue getClibIdentifier() {
      return this.verifastIdentifier;
    }

    public VeriFastExpression getVerifastTerm(List<VeriFastExpression> parameters) {
      if (parameters.size() != 2) {
        //TODO: prop. error handling
        System.err.println("Unexpected number of arguments for binary operator");
      }
      return new VeriFastExpression.BinaryOperation(operation, parameters.get(0), parameters.get(1));
    }

    public List<Sort> getClibParameterTypes() {
      return List.of(this.clibParameterTypes, this.clibParameterTypes);
    }

    public List<VeriFastType> getVerifastParameterTypes() {
      return List.of(this.verifastParameterTypes, this.verifastParameterTypes);
    }

    public Sort getClibResultType() {
      return this.clibResultType;
    }

    public VeriFastType getVerifastResultType() {
      return this.verifastResultType;
    }
  }

  public record FixpointOperatorTranslation(
      Term.Identifier.IdentifierValue verifastIdentifier,
      String operation,
      List<Sort> clibParameterTypes,
      List<VeriFastType> verifastParameterTypes,
      Sort clibResultType,
      VeriFastType verifastResultType) implements TermTranslation {

    public Term.Identifier.IdentifierValue getClibIdentifier() {
      return this.verifastIdentifier;
    }

    public VeriFastExpression getVerifastTerm(List<VeriFastExpression> parameters) {
      return new VeriFastExpression.Fixpoint(operation, parameters);
    }

    public List<Sort> getClibParameterTypes() {
      return this.clibParameterTypes;
    }

    public List<VeriFastType> getVerifastParameterTypes() {
      return this.verifastParameterTypes;
    }

    public Sort getClibResultType() {
      return this.clibResultType;
    }

    public VeriFastType getVerifastResultType() {
      return this.verifastResultType;
    }
  }

  public record VeriFastExpressionTranslation(
      Term.Identifier.IdentifierValue verifastIdentifier,
      Custom expression,
      List<Sort> clibParameterTypes,
      List<VeriFastType> verifastParameterTypes,
      Sort clibResultType,
      VeriFastType verifastResultType) implements TermTranslation {

    @FunctionalInterface
    public interface Custom {
      VeriFastExpression getExpression(List<VeriFastExpression> parameters);
    }

    public Term.Identifier.IdentifierValue getClibIdentifier() {
      return this.verifastIdentifier;
    }

    public VeriFastExpression getVerifastTerm(List<VeriFastExpression> parameters) {
      return expression.getExpression(parameters);
    }

    public List<Sort> getClibParameterTypes() {
      return this.clibParameterTypes;
    }

    public List<VeriFastType> getVerifastParameterTypes() {
      return this.verifastParameterTypes;
    }

    public Sort getClibResultType() {
      return this.clibResultType;
    }

    public VeriFastType getVerifastResultType() {
      return this.verifastResultType;
    }
  }
}
