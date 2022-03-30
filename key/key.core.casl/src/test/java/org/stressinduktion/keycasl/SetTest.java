package org.stressinduktion.keycasl;

import org.junit.jupiter.api.Test;
import de.uka.ilkd.key.casl.main.Util;

import java.io.IOException;
import java.net.URISyntaxException;
import java.nio.file.Path;
import java.util.logging.Logger;

public class SetTest {
    private static final Logger LOGGER = Util.getLogger(SetTest.class);

    @Test
    public void testSet() throws IOException, InterruptedException, URISyntaxException {
        Path source = Path.of(this.getClass().getResource("set/set.casl").toURI());
        Path reference = Path.of(this.getClass().getResource("set/set.key").toURI());
        TestCommon.process(LOGGER, source, reference, null);
    }
}
