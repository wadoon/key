package org.stressinduktion.keycasl;

import de.uka.ilkd.key.nparser.KeyIO;
import org.junit.jupiter.api.Assertions;
import de.uka.ilkd.key.casl.main.CaslFacade;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.logging.Logger;

public class TestCommon {
    public static void process(Logger logger, Path source, Path reference, String problem) throws IOException, InterruptedException {
        String taclet = CaslFacade.process(source, problem);
        String ref = Files.readString(reference);
        logger.info("\n" + taclet);
        new KeyIO().load(taclet).parseFile();
        Assertions.assertEquals(ref, taclet);
    }
}
