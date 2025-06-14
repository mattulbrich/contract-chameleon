package org.contract_lib.lang.key.ast;

import java.util.List;

public record KeyDatatypeConstructor(
  String name,
  List<KeyArgument> arguments
) {}
