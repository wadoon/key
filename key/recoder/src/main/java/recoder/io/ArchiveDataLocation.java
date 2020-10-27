package recoder.io;

import java.io.*;
import java.util.zip.ZipEntry;
import java.util.zip.ZipFile;

public class ArchiveDataLocation implements DataLocation {
    public static final String LOCATION_TYPE_ARCHIVE = "ARCHIVE";

    ZipFile archiveFile;

    String itemName;

    public ArchiveDataLocation(ZipFile archive, String itemname) {
        this.archiveFile = archive;
        this.itemName = itemname;
    }

    public ArchiveDataLocation(String archivename, String itemname) throws IOException {
        this(new ZipFile(archivename), itemname);
    }

    public String getType() {
        return "ARCHIVE";
    }

    public ZipFile getFile() {
        return this.archiveFile;
    }

    public String toString() {
        return getType() + ":" + this.archiveFile.getName() + "?" + this.itemName;
    }

    public boolean hasReaderSupport() {
        return true;
    }

    public InputStream getInputStream() throws IOException {
        InputStream result = null;
        ZipEntry ze = this.archiveFile.getEntry(this.itemName);
        result = new BufferedInputStream(this.archiveFile.getInputStream(ze));
        return result;
    }

    public void inputStreamClosed() {
    }

    public Reader getReader() throws IOException {
        return new InputStreamReader(getInputStream());
    }

    public void readerClosed() {
        inputStreamClosed();
    }

    public boolean isWritable() {
        return false;
    }

    public boolean hasWriterSupport() {
        return false;
    }

    public OutputStream getOutputStream() {
        return null;
    }

    public void outputStreamClosed() {
    }

    public Writer getWriter() {
        return null;
    }

    public void writerClosed() {
    }

    public boolean equals(Object ob) {
        if (ob instanceof ArchiveDataLocation)
            return this.archiveFile.equals(((ArchiveDataLocation) ob).archiveFile);
        return false;
    }

    public int hashCode() {
        return this.archiveFile.hashCode();
    }
}
