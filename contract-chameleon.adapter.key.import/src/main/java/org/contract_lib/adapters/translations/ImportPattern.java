package org.contract_lib.adapters.translations;

import java.util.List;
import java.util.Optional;

import org.contract_lib.lang.contract_lib.ast.Abstraction;
import org.contract_lib.lang.contract_lib.ast.Contract;

import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;

public interface ImportPattern {
  void translate(
      Optional<String> packageName,
      List<Abstraction> abstractions,
      List<Contract> contracts,
      ClassOrInterfaceDeclaration classDec);
}
