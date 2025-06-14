
package org.contract_lib.adapters.translations.contracts;

import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import org.contract_lib.adapters.translations.types.ImportTypeTranslator;
import org.contract_lib.lang.contract_lib.ast.Contract;
import org.contract_lib.lang.contract_lib.ast.Sort;

import com.github.javaparser.ast.body.MethodDeclaration;

public final class ImportContractTranslator {

  private final List<ImportContractTranslation> contractTranslations;

  public ImportContractTranslator(
      List<ImportContractTranslation> contractTranslations) {
    this.contractTranslations = contractTranslations;
  }

  public void translate(
      Sort classSort,
      String methodName,
      List<Contract> contracts,
      MethodDeclaration methodDeclaration) {

    List<Contract> foundContracts = contractTranslations.stream()
        .map(t -> t.translate(classSort, methodName, methodDeclaration))
        .filter(Optional::isPresent)
        .map(Optional::get)
        .collect(Collectors.toList());
    if (foundContracts.isEmpty()) {
      System.err.println("The methdo could not be translated to a contract: " + methodDeclaration);
      return;
    }
    if (foundContracts.size() > 2) {
      System.err.println("The contract of the method is ambiguous, found:" + foundContracts);
      return;
    }
    contracts.add(foundContracts.get(0));
  }

}
