package de.uka.ilkd.key.proof.io;

import java.io.*;
import java.net.URL;
import java.nio.ByteBuffer;

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
        long start = System.nanoTime();
        try(final InputStream input = url.openStream()) {
            long localNumberOfBytes = 0;
            buffer = input.readAllBytes();
            input.close();
            long stop = System.nanoTime();
            System.out.println("UrlRuleSource.countBytesByReadingStream: " + (stop - start) + " ns");
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
            if(buffer!=null)
                return new ByteArrayInputStream(buffer);
            return url.openStream();
        } catch (final IOException exception) {
            throw new RuntimeException("Error while reading rules.", exception);
        }
    }

    @Override
    public String toString() {
        return url.toString();
    }
}
