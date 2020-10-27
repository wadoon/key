package recoder.io;

import recoder.util.FileCollector;
import recoder.util.StringUtils;

import java.io.File;
import java.io.FilenameFilter;
import java.io.IOException;
import java.util.*;
import java.util.zip.ZipEntry;
import java.util.zip.ZipFile;

public class PathList {
    private static final File NO_FILE = new File("");
    private final Set<String> notFound = new HashSet<String>();
    private final Map<String, DataLocation> locations = new HashMap<String, DataLocation>();
    private final List<Object> paths = new ArrayList();
    private final Map<File, Set<String>> dirContents = new HashMap<File, Set<String>>();
    private final Map<File, File> knownDirs = new HashMap<File, File>();

    public PathList() {
    }

    public PathList(String pathStr) {
        add(pathStr);
    }

    public PathList(String[] paths) {
        for (int i = 0; i < paths.length; i++)
            add(paths[i]);
    }

    public void flushCaches() {
        this.dirContents.clear();
        this.knownDirs.clear();
        this.notFound.clear();
    }

    private void addPath(String path) {
        File f = new File(path);
        if (f.isFile()) {
            try {
                this.paths.add(new ZipFile(f));
            } catch (IOException ioe) {
            }
        } else if (f.isDirectory()) {
            this.paths.add(f);
        }
    }

    public int add(String pathStr) {
        int result = 0;
        if (pathStr != null) {
            String[] split_paths = StringUtils.split(pathStr, File.pathSeparatorChar);
            result = split_paths.length;
            for (int i = 0; i < result; i++) {
                String path = split_paths[i].trim();
                if (!path.equals(""))
                    addPath(path);
            }
            this.notFound.clear();
        }
        return result;
    }

    protected Set getContents(File directory) {
        Set<String> result = this.dirContents.get(directory);
        if (result == null) {
            this.dirContents.put(directory, result = new HashSet<String>());
            String[] list = null;
            list = directory.list();
            for (int i = 0; i < list.length; i++)
                result.add(list[i]);
        }
        return result;
    }

    private File getDir(File parent, String name) {
        File attempt = new File(parent, name);
        File result = this.knownDirs.get(attempt);
        if (result == null) {
            result = attempt;
            if (!result.exists())
                result = NO_FILE;
            this.knownDirs.put(attempt, result);
        }
        return (result == NO_FILE) ? null : result;
    }

    private DataLocation getLocation(Object p, String relativeName) {
        if (p instanceof ZipFile) {
            ZipFile zf = (ZipFile) p;
            if (zf.getEntry(relativeName) != null)
                return new ArchiveDataLocation(zf, relativeName);
            String hs = relativeName.replace(File.separatorChar, '/');
            if (zf.getEntry(hs) != null)
                return new ArchiveDataLocation(zf, hs);
        } else if (p instanceof File) {
            File dir = (File) p;
            int sep = relativeName.lastIndexOf(File.separatorChar);
            if (sep >= 0) {
                dir = getDir(dir, relativeName.substring(0, sep));
                if (dir == null)
                    return null;
                relativeName = relativeName.substring(sep + 1);
            }
            if (getContents(dir).contains(relativeName))
                return new DataFileLocation(new File(dir, relativeName));
        }
        return null;
    }

    public DataLocation find(String relativeName) {
        DataLocation result = this.locations.get(relativeName);
        if (result == null && !this.notFound.contains(relativeName)) {
            for (int i = 0; result == null && i < this.paths.size(); i++)
                result = getLocation(this.paths.get(i), relativeName);
            if (result != null) {
                this.locations.put(relativeName, result);
            } else {
                this.notFound.add(relativeName);
            }
        }
        return result;
    }

    public String getRelativeName(String absoluteFilename) {
        for (int i = 0; i < this.paths.size(); i++) {
            Object o = this.paths.get(i);
            if (o instanceof File) {
                File p = (File) o;
                if (p.isDirectory()) {
                    String pathfilename = p.getAbsolutePath();
                    if (absoluteFilename.startsWith(pathfilename)) {
                        int pathfilenamelen = pathfilename.length();
                        if (absoluteFilename.length() == pathfilenamelen)
                            return ".";
                        if (pathfilename.charAt(pathfilenamelen - 1) != File.separatorChar)
                            pathfilenamelen++;
                        return absoluteFilename.substring(pathfilenamelen);
                    }
                }
            }
        }
        return absoluteFilename;
    }

    public DataLocation[] findAll(String relativeName) {
        DataLocation[] tmpRes = new DataLocation[this.paths.size()];
        int count = 0;
        for (int i = 0; i < this.paths.size(); i++) {
            DataLocation dl = getLocation(this.paths.get(i), relativeName);
            if (dl != null)
                tmpRes[count++] = dl;
        }
        DataLocation[] result = new DataLocation[count];
        System.arraycopy(tmpRes, 0, result, 0, count);
        return result;
    }

    public DataLocation[] findAll(FilenameFilter filter) {
        List<DataLocation> res = new ArrayList<DataLocation>();
        for (int i = 0, s = this.paths.size(); i < s; i++) {
            Object f = this.paths.get(i);
            if (f instanceof ZipFile) {
                ZipFile zf = (ZipFile) f;
                Enumeration<? extends ZipEntry> enum2 = zf.entries();
                while (enum2.hasMoreElements()) {
                    ZipEntry e = enum2.nextElement();
                    String name = e.getName();
                    if (filter.accept(null, name)) {
                        DataLocation loc = this.locations.get(name);
                        if (loc == null) {
                            loc = new ArchiveDataLocation(zf, name);
                            this.locations.put(name, loc);
                        }
                        res.add(loc);
                    }
                }
            } else {
                File fi = (File) f;
                if (fi.exists()) {
                    FileCollector fc = new FileCollector(fi);
                    while (fc.next(filter)) {
                        File file = fc.getFile();
                        try {
                            String name = file.getCanonicalPath();
                            DataLocation loc = this.locations.get(name);
                            if (loc == null) {
                                loc = new DataFileLocation(file);
                                this.locations.put(name, loc);
                            }
                            res.add(loc);
                        } catch (IOException ioe) {
                        }
                    }
                }
            }
        }
        DataLocation[] result = new DataLocation[res.size()];
        res.toArray(result);
        return result;
    }

    public String toString() {
        String result;
        if (this.paths.isEmpty()) {
            result = "";
        } else {
            StringBuffer sb = new StringBuffer();
            for (int i = 0; i < this.paths.size(); i++) {
                sb.append(File.pathSeparatorChar);
                Object f = this.paths.get(i);
                if (f instanceof ZipFile) {
                    sb.append(((ZipFile) f).getName());
                } else {
                    sb.append(((File) f).getPath());
                }
            }
            result = sb.toString().substring(1);
        }
        return result;
    }
}
