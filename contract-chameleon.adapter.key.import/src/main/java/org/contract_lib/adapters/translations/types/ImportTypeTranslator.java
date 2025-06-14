package org.contract_lib.adapters.translations.types;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import com.github.javaparser.ast.type.Type;

public final class ImportTypeTranslator {

  private final Map<Type, ImportTypeTranslationResult> translations;

  public ImportTypeTranslator(List<ImportTypeTranslation> translation) {
    this.translations = new HashMap<>();
    translation.forEach(this::addTranslation);
  }

  public void addTranslation(ImportTypeTranslation translation) {
    this.translations.put(translation.getJavaType(),
        new ImportTypeTranslationResult(translation.getSort(),
            translation.requiredHelper("t", translation.getJavaType())));
  }

  public Optional<ImportTypeTranslationResult> translateType(Type type) {
    ImportTypeTranslationResult res = this.translations.get(type);
    if (res == null) {
      return Optional.empty();
    } else {
      return Optional.of(res);
    }
  }

}
