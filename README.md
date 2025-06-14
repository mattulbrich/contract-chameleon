# Contract-Chameleon

A translation tool for Contract-LIB.

## Executing the tool

The tool with all default adapters can be run with:

```sh
java -jar contract-chameleon-exe.jar
```

## Add own Adapters

Place the `JAR` of the additional adapter next to the `contract-chameleon-cl.jar`

```sh
java -cp '*' org.contractlib.ContractChameleon
```

The additional `JAR` must have a `org.contractlib.contract_chameleon.Adapter`
file in `src/main/ressources/META-INF/services`
containing the full class name (including package) of the additional adapter.
Compare the following [example](./contract-chameleon.adapter.key-provider/).

## Developing the tool

- Install git submodules

```sh
cd _ContractChameleon
git submodule update --init --recursive # to fetch and initialize the submodules the first time 
git pull --recurse-submodules # to pull changes from submodules

```

- Publish custom JML-Parser

```
./mvnw clean install -DskipTests
ls ~/.m2/repository/io/github/jmltoolkit/jmlparser-core/ #check that snapshot exists
```

- Build with gradle

```sh
gradle clean build
gradle run --args="<adapter-name> <file_path>"
gradle run-integration-tests #Simple way to check if the adapter do what they should
```

- Run integration tests

```sh
gradle key_ci-check-all --continue
```
