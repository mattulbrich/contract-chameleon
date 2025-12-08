package org.contract_lib.contract_chameleon;

import java.util.Optional;

public interface AdapterArgumentProvider {
  <A extends AdapterArgument> Optional<A> getAdapterArgument(Class<A> adapterClass);
}
