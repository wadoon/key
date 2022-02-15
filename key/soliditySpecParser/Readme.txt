Experimental Solidity specification compiler


export SOLIDIKEY=~/key/solidiKeY/key
ln -s $SOLIDIKEY/soliditySpecParser/include CONTRACTDIRECTORY/include

Compile:
in solidiKeY/key/soliditySpecParser, execute:
javac -cp $SOLIDIKEY/key.core/lib/antlr-4.9.3-complete.jar:$SOLIDIKEY/key.core/build/libs/key.core-2.7.jar:. Solidity*.java

Run:
java SoliditySpecCompiler [.sol file] [contract name] [function name]

A .key-formatted file with proof obligations for [function name] will be printed to stdout. For constructor proof obligations, use [contract name] as function name.

LOTS of limitations at the moment.




java -cp $SOLIDIKEY/key.core/lib/antlr-4.9.3-complete.jar:$SOLIDIKEY/key.core/build/libs/key.core-2.7.jar:$SOLIDIKEY/soliditySpecParser SoliditySpecCompiler [.sol file] [contract name] [function name]

