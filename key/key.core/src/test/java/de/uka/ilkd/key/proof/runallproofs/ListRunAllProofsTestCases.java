package de.uka.ilkd.key.proof.runallproofs;

import de.uka.ilkd.key.proof.runallproofs.proofcollection.ProofGroup;
import org.antlr.runtime.RecognitionException;

import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

/**
 * Used by {@link RunAllProofsTest} command line interface to print out a list
 * of test cases. Command line interface can be found at git location:<br>
 * key/scripts/runAllProofs
 *
 * @author Kai Wallisch
 * @see RunAllProofsTestSuite
 * @see RunAllProofsTest
 */
public class ListRunAllProofsTestCases {
    public static void main(String[] args) throws IOException, RecognitionException {
        List<ProofGroup> units = new LinkedList<ProofGroup>();
        units.addAll(ProofCollections.getJavaDlProofCollection().createRunAllProofsTestUnits());
        units.addAll(ProofCollections.getInfFlowCollection().createRunAllProofsTestUnits());
        for (ProofGroup unit : units) {
            System.out.println(unit.getGroupName());
        }
    }
}