
package org.contract_lib.adapters.translations.contracts;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import org.contract_lib.lang.contract_lib.ast.Formal;
import org.contract_lib.lang.contract_lib.ast.Symbol;
import org.contract_lib.lang.contract_lib.ast.Sort;
import org.contract_lib.lang.contract_lib.ast.ArgumentMode;
import org.contract_lib.adapters.translations.types.ImportTypeTranslationResult;
import org.contract_lib.adapters.translations.types.ImportTypeTranslator;

import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.jml.clauses.JmlClause;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.ast.type.Type;

public final class ContractArgumentsExtractor {

  private static final String RESULT_IDENTIFIER = "result";
  private static final String FOOTPRINT_IDENTIFIER = "footprint";

  private final ImportTypeTranslator typeTranslator;

  public ContractArgumentsExtractor(
      ImportTypeTranslator typeTranslator) {
    this.typeTranslator = typeTranslator;
  }

  public List<Formal> extractArguments(
      NodeList<Parameter> arguments,
      Type returnType,
      List<JmlClause> accessibleClauses,
      List<JmlClause> assignableClauses) {

    ArrayList<Formal> formals = new ArrayList<>();

    translateReturn(returnType, accessibleClauses, assignableClauses)
        .ifPresent(formals::add);

    arguments.stream()
        .map((a) -> this.translateArgument(a, accessibleClauses, assignableClauses))
        .filter(Optional::isPresent)
        .map(Optional::get)
        .forEachOrdered(formals::add);

    return formals;
  }

  public Optional<Formal> translateArgument(
      Parameter argument,
      List<JmlClause> accessibleClauses,
      List<JmlClause> assignableClauses) {

    Symbol name = new Symbol(argument.getNameAsString());

    Optional<ImportTypeTranslationResult> typeRes = this.typeTranslator.translateType(argument.getType());

    boolean isAssignable = seachFootprint(accessibleClauses, argument.getNameAsString());

    if (isAssignable) {
      return typeRes.map((res) -> new Formal(name, ArgumentMode.INOUT, res.sort()));
    } else {
      return typeRes.map((res) -> new Formal(name, ArgumentMode.IN, res.sort()));
    }
  }

  public Optional<Formal> translateReturn(Type type,
      List<JmlClause> accessibleClauses,
      List<JmlClause> assignableClauses) {

    if (type.isVoidType()) {
      if (!accessibleClauses.isEmpty()) {
        System.err.println("If a return type is void, no accessible terms are allowed.");
      }
      return Optional.empty();
    }

    Optional<Formal> pt = type.toPrimitiveType()
        .flatMap((p) -> this.translateReturnPrimitiveType(p, accessibleClauses, assignableClauses));

    if (pt.isPresent()) {
      return pt;
    }

    return type.toClassOrInterfaceType()
        .flatMap((p) -> this.translateReturnClassType(p, accessibleClauses, assignableClauses));
  }

  private Optional<Formal> translateReturnClassType(ClassOrInterfaceType classOrInterfaceType,
      List<JmlClause> accessibleClauses,
      List<JmlClause> assignableClauses) {
    Optional<ImportTypeTranslationResult> tres = typeTranslator.translateType(classOrInterfaceType);

    if (tres.isEmpty()) {
      System.err.println("could not translate type: " + classOrInterfaceType + " " + classOrInterfaceType.scope());
    }

    return tres.map((res) -> new Formal(new Symbol(RESULT_IDENTIFIER), ArgumentMode.INOUT, res.sort()));
  }

  private Optional<Formal> translateReturnPrimitiveType(PrimitiveType primitiveType, List<JmlClause> accessibleClauses,
      List<JmlClause> assignableClauses) {
    Optional<ImportTypeTranslationResult> tres = typeTranslator.translateType(primitiveType);
    if (tres.isEmpty()) {
      System.err.println("Could not translate type: " + primitiveType);
    }

    return tres.map((res) -> new Formal(new Symbol(RESULT_IDENTIFIER), ArgumentMode.OUT, res.sort()));
  }

  public boolean seachFootprint(List<JmlClause> clauses, String name) {
    return clauses.stream().anyMatch((c) -> matchFootprint(c, name));
  }

  private boolean matchFootprint(JmlClause clause, String name) {
    return clause.toJmlMultiExprClause().map(me -> matchExpressions(me.getExpressions(), name)).orElse(false);
  }

  private boolean matchExpressions(NodeList<Expression> expressions, String name) {
    return expressions.stream().anyMatch(e -> this.matchFootprintExpression(e, name));
  }

  private boolean matchFootprintExpression(Expression expression, String name) {
    return expression.toFieldAccessExpr()
        .filter(f -> f.getNameAsString().equals(FOOTPRINT_IDENTIFIER))
        .map(f -> f.getScope())
        .map(e -> matchNameExpression(e, name)).orElse(false);
  }

  private boolean matchNameExpression(Expression expression, String name) {
    return expression.toNameExpr().map((n) -> n.getNameAsString().equals(name)).orElse(false);
  }
}
