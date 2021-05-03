Experimental Solidity specification compiler

Compile:
javac Solidity*.java

Run:
java SoliditySpecCompiler [.sol file] [contract name] [function name]

A .key-formatted file with proof obligations for [function name] will be printed to stdout. For constructor proof obligations, use [contract name] as function name.

LOTS of limitations at the moment.

