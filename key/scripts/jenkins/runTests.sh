#!/bin/sh -x
unset DISPLAY
export KEY_VERSION="2.7.$BUILD_NUMBER"
export PATH=$PATH:/home/hudson/key/bin/
export STATISTICS_DIR="$JENKINS_HOME/userContent/statistics-$JOB_NAME"

function runTests {
    (cd $1; shift;
     ./start.sh  -Xmx4g -XX:MaxPermSize=256m -ea -Dkey.disregardSettings=true \
                 org.junit.runner.JUnitCore  \
                 $@
     )
}



#
# Run unit tests
#
cd key
./gradlew --continue compileTestJava genTest

runTests key.core \
         de.uka.ilkd.key.suite.TestKey

runTests key.core.symbolic_execution \
         de.uka.ilkd.key.symbolic_execution.suite.AllSymbolicExecutionTests

runTests key.core.testgen \
         de.uka.ilkd.key.suite.AllTestGenTests

runTests key.core.proof_references \
         de.uka.ilkd.key.proof_references.suite.AllProofReferencesTests

#runTests key.core \
#         de.uka.ilkd.key.proof.runallproofs.RunAllProofsTestSuite

#runTests key.core \
#         de.uka.ilkd.key.proof.proverules.ProveRulesTest

EXIT_UNIT_TESTS=$?

# Adapt to old scheme. copy tests xml to a folder where jenkins find them.
# Change if there is no ant build.
# Old regex: key/**/testresults/*.xml
XMLTESTFOLDER="xxx/testresults"
rm -rf $XMLTESTFOLDER
mkdir -p $XMLTESTFOLDER
find -iname 'TEST-*.xml' -exec cp {} $XMLTESTFOLDER \;

#
# create statistics if successful
#
mkdir -p "$STATISTICS_DIR"
# just for testing purposes  commented out
if [ "$EXIT_UNIT_TESTS" -eq "0" ]
then 
  cp ../key.core.test/testresults/runallproofs/runStatistics.csv "$STATISTICS_DIR/$BUILD_NUMBER.csv"
  exit 0
else 
  exit 1
fi

