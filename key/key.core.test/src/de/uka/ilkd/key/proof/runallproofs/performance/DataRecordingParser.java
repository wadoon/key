package de.uka.ilkd.key.proof.runallproofs.performance;

import java.io.File;

import org.antlr.runtime.TokenStream;

import de.uka.ilkd.key.proof.runallproofs.proofcollection.ProofCollectionParser;
import de.uka.ilkd.key.proof.runallproofs.proofcollection.ProofCollectionSettings;
import de.uka.ilkd.key.proof.runallproofs.proofcollection.TestFile;
import de.uka.ilkd.key.proof.runallproofs.proofcollection.TestProperty;

public class DataRecordingParser extends ProofCollectionParser {

    private final File dataDir;

    public DataRecordingParser(TokenStream input, File dataDir) {
        super(input);
        this.dataDir = dataDir;
    }

    @Override
    public TestFile getTestFile(TestProperty testProperty, String path, ProofCollectionSettings settings) {
        return new DataRecordingTestFile(testProperty, path, settings, dataDir);
    }
}