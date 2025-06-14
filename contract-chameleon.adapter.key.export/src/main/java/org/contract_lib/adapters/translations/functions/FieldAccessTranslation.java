package org.contract_lib.adapters.translations.functions;

import java.util.List;

import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.ast.expr.SimpleName;

import com.github.javaparser.ast.type.Type;

import org.contract_lib.adapters.translations.FuncTranslation;
import org.contract_lib.lang.contract_lib.ast.Sort;
import org.contract_lib.lang.contract_lib.ast.Term;

public record FieldAccessTranslation(
    Term.Identifier.IdentifierValue clibFieldIdentifier,
    Sort clibOwnerType,
    Sort clibResultType,
    Type jmlOwnerType,
    Type jmlResultType) implements FuncTranslation {

  public Term.Identifier.IdentifierValue getClibIdentifier() {
    return clibFieldIdentifier;
  }

  public Expression getJmlTerm(List<Expression> parameters) {
    if (parameters.size() != 1) {
      //TODO: Throw proper error
      System.err.println("Field access must only have one owner!");
    }
    Expression scope = parameters.get(0);
    return new FieldAccessExpr(
        scope,
        null,
        new SimpleName(clibFieldIdentifier.identifier().identifier()));
  }

  public List<Sort> getClibParameterTypes() {
    return List.of(
        clibOwnerType);
  }

  public List<Type> getJmlParameterTypes() {
    return List.of(
        jmlOwnerType);
  }

  public Sort getClibResultType() {
    return clibOwnerType;
  }

  public Type getJmlResultType() {
    return jmlResultType;
  }
}
