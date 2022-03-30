package org.stressinduktion.keycasl;

import de.uka.ilkd.key.nparser.KeyIO;
import org.junit.jupiter.api.Assertions;
import org.stressinduktion.keycasl.main.Main;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.logging.Logger;

public class TestCommon {
    public static void process(Logger logger, Path source, Path reference, String problem) throws IOException, InterruptedException {
        String taclet = Main.process(source, problem);
        String ref = Files.readString(reference);
        logger.info("\n" + taclet);
        new KeyIO().load(taclet).parseFile();
        Assertions.assertEquals(ref, taclet);
    }
}
