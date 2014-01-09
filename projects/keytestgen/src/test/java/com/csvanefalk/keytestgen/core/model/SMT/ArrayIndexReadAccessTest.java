package com.csvanefalk.keytestgen.core.model.SMT;

import com.csvanefalk.keytestgen.core.keyinterface.KeYInterfaceException;
import com.csvanefalk.keytestgen.core.model.ModelGeneratorException;
import com.csvanefalk.keytestgen.core.model.ModelTest;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import org.junit.Test;

import java.io.IOException;

/**
 * Created by christopher on 07/01/14.
 */
public class ArrayIndexReadAccessTest extends ModelTest {

    public ArrayIndexReadAccessTest() throws KeYInterfaceException, IOException {
        super("arrays", false, "ArrayIndexReadAccess.java");
    }

    @Test
    public void ArrayIndexWriteAccess() throws ModelGeneratorException, ProofInputException {
        IExecutionNode node = getFirstSymbolicNodeForStatement("ArrayIndexReadAccess.compute", "return 42");
        modelGenerator.generateModel(node);
    }
}
