package org.contract_lib.lang.verifast.ast;

import java.util.List;

public record VeriFastInductionConstructor(
  String name,
  List<VeriFastType> parameters 
) {}
