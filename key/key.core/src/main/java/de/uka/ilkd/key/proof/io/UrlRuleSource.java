package de.uka.ilkd.key.proof.io;

import java.io.*;
import java.net.URL;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class UrlRuleSource extends RuleSource {
    private static final int MAX_BUFFER_SIZE = Integer.MAX_VALUE - 8;
    private static final int DEFAULT_BUFFER_SIZE = 8192;

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
            buffer = readNBytes(input, Integer.MAX_VALUE);
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
            return new BufferedInputStream(url.openStream(), 4096);
        } catch (final IOException exception) {
            throw new RuntimeException("Error while reading rules.", exception);
        }
    }

    @Override
    public String toString() {
        return url.toString();
    }



    /**
     * Reads up to a specified number of bytes from the input stream. This
     * method blocks until the requested number of bytes have been read, end
     * of stream is detected, or an exception is thrown. This method does not
     * close the input stream.
     *
     * <p> The length of the returned array equals the number of bytes read
     * from the stream. If {@code len} is zero, then no bytes are read and
     * an empty byte array is returned. Otherwise, up to {@code len} bytes
     * are read from the stream. Fewer than {@code len} bytes may be read if
     * end of stream is encountered.
     *
     * <p> When this stream reaches end of stream, further invocations of this
     * method will return an empty byte array.
     *
     * <p> Note that this method is intended for simple cases where it is
     * convenient to read the specified number of bytes into a byte array. The
     * total amount of memory allocated by this method is proportional to the
     * number of bytes read from the stream which is bounded by {@code len}.
     * Therefore, the method may be safely called with very large values of
     * {@code len} provided sufficient memory is available.
     *
     * <p> The behavior for the case where the input stream is <i>asynchronously
     * closed</i>, or the thread interrupted during the read, is highly input
     * stream specific, and therefore not specified.
     *
     * <p> If an I/O error occurs reading from the input stream, then it may do
     * so after some, but not all, bytes have been read. Consequently the input
     * stream may not be at end of stream and may be in an inconsistent state.
     * It is strongly recommended that the stream be promptly closed if an I/O
     * error occurs.
     *
     * @implNote
     * The number of bytes allocated to read data from this stream and return
     * the result is bounded by {@code 2*(long)len}, inclusive.
     *
     * @param stream
     * @param len the maximum number of bytes to read
     * @return a byte array containing the bytes read from this input stream
     * @throws IllegalArgumentException if {@code length} is negative
     * @throws IOException if an I/O error occurs
     * @throws OutOfMemoryError if an array of the required size cannot be
     *         allocated.
     *
     * @since 11
     */
    //Backported from Java 11.
    //TODO Remove this function if go Java.
    public byte[] readNBytes(InputStream stream, int len) throws IOException {
        if (len < 0) {
            throw new IllegalArgumentException("len < 0");
        }

        List<byte[]> bufs = null;
        byte[] result = null;
        int total = 0;
        int remaining = len;
        int n;
        do {
            byte[] buf = new byte[Math.min(remaining, DEFAULT_BUFFER_SIZE)];
            int nread = 0;

            // read to EOF which may read more or less than buffer size
            while ((n = stream.read(buf, nread,
                    Math.min(buf.length - nread, remaining))) > 0) {
                nread += n;
                remaining -= n;
            }

            if (nread > 0) {
                if (MAX_BUFFER_SIZE - total < nread) {
                    throw new OutOfMemoryError("Required array size too large");
                }
                total += nread;
                if (result == null) {
                    result = buf;
                } else {
                    if (bufs == null) {
                        bufs = new ArrayList<>();
                        bufs.add(result);
                    }
                    bufs.add(buf);
                }
            }
            // if the last call to read returned -1 or the number of bytes
            // requested have been read then break
        } while (n >= 0 && remaining > 0);

        if (bufs == null) {
            if (result == null) {
                return new byte[0];
            }
            return result.length == total ?
                    result : Arrays.copyOf(result, total);
        }

        result = new byte[total];
        int offset = 0;
        remaining = total;
        for (byte[] b : bufs) {
            int count = Math.min(b.length, remaining);
            System.arraycopy(b, 0, result, offset, count);
            offset += count;
            remaining -= count;
        }

        return result;
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
