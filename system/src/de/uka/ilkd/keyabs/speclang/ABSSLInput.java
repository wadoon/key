package de.uka.ilkd.keyabs.speclang;

import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.AbstractEnvInput;
import de.uka.ilkd.key.proof.io.EnvInput;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.proof.init.ABSInitConfig;

import java.io.File;
import java.util.List;

/**
 * Created with IntelliJ IDEA.
 * User: bubel
 * Date: 28.03.13
 * Time: 17:08
 * To change this template use File | Settings | File Templates.
 */
public class ABSSLInput extends AbstractEnvInput<ABSServices, ABSInitConfig> {
    public ABSSLInput(String path, List<File> classPath, File bootClassPath) {
        super("specification", path, classPath, bootClassPath);
    }

    @Override
    public void read() throws ProofInputException {
    }
}
