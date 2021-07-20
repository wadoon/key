package de.uka.ilkd.key.proof.io;

import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.key_project.util.java.IOUtil;

import java.io.*;
import java.net.URL;
import java.nio.channels.Channels;
import java.nio.channels.ReadableByteChannel;
import java.nio.charset.CodingErrorAction;
import java.nio.charset.StandardCharsets;

public class UrlRuleSource extends RuleSource {

    private byte[] buffer;
    private final URL url;
    private final long numberOfBytes;

    UrlRuleSource(final URL url) {
        this.url = url;
        if ("file".equals(url.getProtocol())) {
            numberOfBytes = new File(url.getFile()).length();
        } else {
            numberOfBytes = countBytesByReadingStream();
        }
    }

    private long countBytesByReadingStream() {
        try (final InputStream input = url.openStream()) {
            buffer = IOUtil.readBytesFrom(input, Integer.MAX_VALUE);
            input.close();
            return buffer.length;
        } catch (final IOException exception) {
            throw new RuntimeException(exception);
        }
    }

    @Override
    public int getNumberOfBytes() {
        return (int) numberOfBytes;
    }

    @Override
    public File file() {
        return new File(url.getFile());
    }

    @Override
    public URL url() {
        return url;
    }

    @Override
    public String getExternalForm() {
        return url.toExternalForm();
    }

    @Override
    public InputStream getNewStream() {
        try {
            if (buffer != null)
                return new ByteArrayInputStream(buffer);
            return new BufferedInputStream(url.openStream(), 4096);
        } catch (final IOException exception) {
            throw new RuntimeException("Error while reading rules.", exception);
        }
    }

    @Override
    public String toString() {
        return url.toString();
    }


    @Override
    public CharStream getCharStream() throws IOException {
        try (ReadableByteChannel channel = Channels.newChannel(getNewStream())) {
            return CharStreams.fromChannel(
                    channel,
                    StandardCharsets.UTF_8,
                    4096,
                    CodingErrorAction.REPLACE,
                    url.toString(),
                    -1);
        }
    }
}
