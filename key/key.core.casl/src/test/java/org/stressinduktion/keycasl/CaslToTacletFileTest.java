package org.stressinduktion.keycasl;

import org.junit.jupiter.api.Test;
import org.stressinduktion.keycasl.main.Main;
import org.stressinduktion.keycasl.main.Util;

import java.io.IOException;
import java.net.URISyntaxException;
import java.nio.file.Path;
import java.util.logging.Logger;

public final class CaslToTacletFileTest {
    private static final Logger LOGGER = Util.getLogger(CaslToTacletFileTest.class);

    @Test
    public void process() throws IOException, URISyntaxException, InterruptedException {
        Path source = Path.of(this.getClass().getResource("reverse/reverse.casl").toURI());
        Path reference = Path.of(this.getClass().getResource("reverse/reverse.key").toURI());
        TestCommon.process(LOGGER, source, reference, null);
    }
}
