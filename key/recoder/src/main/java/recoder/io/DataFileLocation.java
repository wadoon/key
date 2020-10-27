package recoder.io;

import java.io.*;

public class DataFileLocation implements DataLocation {
    public static final String LOCATION_TYPE_FILE = "FILE";

    File file;

    String canonicalPath;

    public DataFileLocation(File f) {
        setFile(f);
    }

    public DataFileLocation(String filename) {
        setFile(new File(filename));
    }

    public String getType() {
        return "FILE";
    }

    public File getFile() {
        return this.file;
    }

    private void setFile(File f) {
        this.file = f;
        try {
            this.canonicalPath = this.file.getCanonicalPath();
        } catch (IOException ioe) {
            this.canonicalPath = this.file.getAbsolutePath();
        }
    }

    public String toString() {
        return getType() + ":" + this.file.getPath();
    }

    public boolean hasReaderSupport() {
        return true;
    }

    public InputStream getInputStream() throws IOException {
        return new BufferedInputStream(new FileInputStream(this.file));
    }

    public void inputStreamClosed() {
    }

    public Reader getReader() throws IOException {
        return new FileReader(this.file);
    }

    public void readerClosed() {
    }

    public boolean isWritable() {
        return true;
    }

    public boolean hasWriterSupport() {
        return true;
    }

    public OutputStream getOutputStream() throws IOException {
        return new FileOutputStream(this.file);
    }

    public void outputStreamClosed() {
    }

    public Writer getWriter() throws IOException {
        return new FileWriter(this.file);
    }

    public void writerClosed() {
    }

    public boolean equals(Object ob) {
        if (ob instanceof DataFileLocation)
            return this.canonicalPath.equals(((DataFileLocation) ob).canonicalPath);
        return false;
    }

    public int hashCode() {
        return this.canonicalPath.hashCode();
    }
}
