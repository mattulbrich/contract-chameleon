
package org.contract_lib.adapters.translations;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import org.contract_lib.adapters.translations.contracts.ImportContractTranslator;
import org.contract_lib.adapters.translations.types.AbstractionTypeTranslation;
import org.contract_lib.adapters.translations.types.ImportTypeTranslationResult;
import org.contract_lib.adapters.translations.types.ImportTypeTranslator;
import org.contract_lib.lang.contract_lib.ast.Abstraction;
import org.contract_lib.lang.contract_lib.ast.Constructor;
import org.contract_lib.lang.contract_lib.ast.Contract;
import org.contract_lib.lang.contract_lib.ast.DatatypeDec;
import org.contract_lib.lang.contract_lib.ast.Numeral;
import org.contract_lib.lang.contract_lib.ast.SelectorDec;
import org.contract_lib.lang.contract_lib.ast.Sort;
import org.contract_lib.lang.contract_lib.ast.Symbol;
import org.contract_lib.lang.contract_lib.ast.SortDec.Def;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.jml.body.JmlClassAccessibleDeclaration;
import com.github.javaparser.ast.jml.body.JmlClassExprDeclaration;
import com.github.javaparser.ast.jml.body.JmlFieldDeclaration;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.Type;

public final class AbstractClassImporter implements ImportPattern {

  private final ImportTypeTranslator typeTranslator;
  private final ImportContractTranslator contractImporter;
  private final List<SelectorDec> selectorDecs;
  private final List<Expression> invariants;

  public AbstractClassImporter(
      ImportTypeTranslator typeTranslator,
      ImportContractTranslator contractImporter) {
    this.typeTranslator = typeTranslator;
    this.contractImporter = contractImporter;
    this.selectorDecs = new ArrayList<>();
    this.invariants = new ArrayList<>();
  }

  public void translate(
      Optional<String> packageName,
      List<Abstraction> abstractions,
      List<Contract> contracts,
      ClassOrInterfaceDeclaration classDec) {
    this.selectorDecs.clear();
    this.invariants.clear();
    if (!isValidAbstractClass(classDec)) {
      return;
    }
    translateAbstraction(packageName, abstractions, contracts, classDec);
  }

  private boolean isValidAbstractClass(ClassOrInterfaceDeclaration classDec) {
    boolean success = true;
    if (!classDec.isAbstract()) {
      success = false;
      System.err.println("Imported class must be abstract.");
    }
    if (!classDec.isPublic()) {
      success = false;
      System.err.println("Imported class must be public.");
    }

    return success;
  }

  private void translateAbstraction(
      Optional<String> packageName,
      List<Abstraction> abstractions,
      List<Contract> contracts,
      ClassOrInterfaceDeclaration classDec) {

    String name = packageName
        .map(pn -> pn + "." + classDec.getNameAsString())
        .orElse(classDec.getNameAsString());

    Sort classSort = new Sort.Type(name);

    this.typeTranslator.addTranslation(
        new AbstractionTypeTranslation(name, new ClassOrInterfaceType(null, classDec.getNameAsString())));

    System.err.println("Class found with identifier: " + name);

    // Fetch all fields
    classDec.members().stream()
        .forEach(f -> f.ifJmlFieldDeclaration(this::translateJMLFieldDeclaration));

    // Check invariants
    classDec.members()
        .forEach(f -> f.ifJmlClassExprDeclaration(this::translateJmlClassExprDeclaration));

    // Check accessible clauses
    classDec.members()
        .forEach(f -> f.ifJmlClassAccessibleDeclaration(this::translateJmlClassAccessibleDeclaration));

    if (this.invariants.isEmpty()) {
      Constructor c = new Constructor(new Symbol(classDec.getNameAsString()), new ArrayList<>(this.selectorDecs));
      Def def = new Def(new Symbol(name), new Numeral("0"));
      DatatypeDec datatype = new DatatypeDec(List.of(), List.of(c));
      Abstraction abstraction = new Abstraction(def, datatype);
      abstractions.add(abstraction);
    } else {
      System.err.println("The following invariants are not provided" + this.invariants);
    }

    // Fetch contracts

    classDec.members()
        .forEach(f -> f.ifMethodDeclaration(m -> this.translateMethodDeclaration(classSort, name, contracts, m)));

    //TODO: check for error
    classDec.members()
        .forEach(this::bodyTranlsation);
  }

  private void bodyTranlsation(BodyDeclaration<?> bodyDec) {
    if (bodyDec.isJmlFieldDeclaration()) {
      //bodyDec.ifJmlFieldDeclaration(this::translateJMLFieldDeclaration);
    } else if (bodyDec.isJmlClassAccessibleDeclaration()) {
      //bodyDec.ifJmlClassAccessibleDeclaration(this::translateJmlClassAccessibleDeclaration);
    } else if (bodyDec.isMethodDeclaration()) {
      //bodyDec.ifMethodDeclaration(this::translateMethodDeclaration);
    } else if (bodyDec.isJmlClassExprDeclaration()) {
      //bodyDec.ifJmlClassExprDeclaration(this::translateJmlClassExprDeclaration);
    } else {
      //TODO: Add proper error
      System.err.println("Unsupported Class level declaration:");
      System.err.println(bodyDec);
      System.err.println(bodyDec.getClass());
    }
  }

  private void translateJmlClassExprDeclaration(JmlClassExprDeclaration classExpr) {
    System.err.println("Class Invariant: " + classExpr);
  }

  private boolean checkForInstanceGhostField(JmlFieldDeclaration fieldDeclaration) {
    if (!fieldDeclaration.getDecl().getModifiers().contains(new Modifier(Modifier.DefaultKeyword.JML_GHOST))) {
      return false;
    }
    if (!fieldDeclaration.getDecl().getModifiers().contains(new Modifier(Modifier.DefaultKeyword.JML_INSTANCE))) {
      return false;
    }
    return true;
  }

  private void translateJMLFieldDeclaration(JmlFieldDeclaration fieldDeclaration) {
    if (checkForInstanceGhostField(fieldDeclaration)) {
      FieldDeclaration f = fieldDeclaration.getDecl();
      NodeList<VariableDeclarator> variables = f.getVariables();
      variables.forEach(this::translateVariableDeclarator);
    }
  }

  private void translateVariableDeclarator(VariableDeclarator variableDeclarator) {
    String name = variableDeclarator.getNameAsString();
    Type type = variableDeclarator.getType();
    Optional<ImportTypeTranslationResult> trans = this.typeTranslator.translateType(type);
    trans.ifPresent(s -> this.translateSelector(name, s));
    if (trans.isEmpty()) {
      //TODO: proper error handling
      System.err.println(String.format("Found ghost field '%s' of type '%s', which is not supported.", name, type));
    }
  }

  private void translateSelector(String name, ImportTypeTranslationResult trans) {
    this.selectorDecs.add(new SelectorDec(new Symbol(name), trans.sort()));
    this.invariants.addAll(trans.expressions());
  }

  private void translateJmlClassAccessibleDeclaration(JmlClassAccessibleDeclaration classDec) {
    System.err.println("Class accessible: " + classDec);

    boolean isThis = classDec.getExpressions()
        .stream()
        .map(Expression::toFieldAccessExpr)
        .filter(Optional::isPresent)
        .map(Optional::get)
        .map(FieldAccessExpr::getScope)
        .filter(Expression::isThisExpr)
        .findFirst()
        .isPresent();

    List<String> scope = classDec.getExpressions()
        .stream()
        .map(Expression::toFieldAccessExpr)
        .filter(Optional::isPresent)
        .map(Optional::get)
        .map(FieldAccessExpr::getScope)
        .map(Expression::toNameExpr)
        .filter(Optional::isPresent)
        .map(Optional::get)
        .map(NameExpr::getNameAsString)
        .collect(Collectors.toList());

    System.err.println("Accessible dec" + scope);
  }

  private void translateMethodDeclaration(
      Sort classSort,
      String classIdentifier,
      List<Contract> contracts,
      MethodDeclaration method) {

    String methodIdentifier = classIdentifier + "." + method.getNameAsString();

    this.contractImporter.translate(classSort, methodIdentifier, contracts, method);
  }
}
