Experimental Solidity specification compiler

Compile:
javac Solidity*.java

Run:
java SoliditySpecCompiler [.sol file] [function name]

A .key-formatted file with proof obligations for [function name] will be printed to stdout. For constructor proof obligations, use [contract name] + "Impl".

Only accepts one class. LOTS of other limitations at the moment.

