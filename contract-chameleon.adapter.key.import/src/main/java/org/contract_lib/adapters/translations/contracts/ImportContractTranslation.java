
package org.contract_lib.adapters.translations.contracts;

import java.util.Optional;

import org.contract_lib.lang.contract_lib.ast.Contract;
import org.contract_lib.lang.contract_lib.ast.Sort;

import com.github.javaparser.ast.body.MethodDeclaration;

public interface ImportContractTranslation {

  Optional<Contract> translate(
      Sort classSort,
      String methodName,
      MethodDeclaration methodDeclaration);
}
