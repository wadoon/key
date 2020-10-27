package recoder.io;

import java.io.*;

public interface DataLocation {
    String getType();

    String toString();

    boolean hasReaderSupport();

    InputStream getInputStream() throws IOException;

    void inputStreamClosed();

    Reader getReader() throws IOException;

    void readerClosed();

    boolean isWritable();

    boolean hasWriterSupport();

    OutputStream getOutputStream() throws IOException;

    void outputStreamClosed();

    Writer getWriter() throws IOException;

    void writerClosed();
}
