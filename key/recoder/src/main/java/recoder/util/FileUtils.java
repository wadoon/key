package recoder.util;

import java.io.File;
import java.io.IOException;
import java.util.StringTokenizer;

public class FileUtils {
    private static final String ARCHIVE_NAME;
    private static final String LIB_SUBDIR;
    private static File userDirectory;

    static {
        if (System.getProperty("os.name").startsWith("Mac")) {
            ARCHIVE_NAME = "classes.jar";
            LIB_SUBDIR = "../Classes";
        } else if (System.getProperty("java.version").startsWith("1.1")) {
            ARCHIVE_NAME = "classes.zip";
            LIB_SUBDIR = "lib";
        } else {
            ARCHIVE_NAME = "rt.jar";
            LIB_SUBDIR = "lib";
        }
    }

    public static File getUserDirectory() {
        if (userDirectory == null)
            userDirectory = new File(System.getProperty("user.dir"));
        return userDirectory;
    }

    public static String getRelativePath(File start, File dest) {
        String startname, destname;
        if (start.isFile())
            start = new File(start.getParent());
        try {
            startname = start.getCanonicalPath();
            destname = dest.getCanonicalPath();
        } catch (IOException ioe) {
            return dest.getAbsolutePath();
        }
        if (startname.equals(destname))
            return ".";
        int slen = startname.length();
        int dlen = destname.length();
        int maxlen = Math.min(slen, dlen);
        int index;
        for (index = 0; index < maxlen &&
                startname.charAt(index) == destname.charAt(index); index++)
            ;
        if (index <= 1)
            return destname;
        StringBuffer result = new StringBuffer();
        if (index != slen) {
            while (index > 0 && startname.charAt(index) != File.separatorChar)
                index--;
            index++;
            result.append("..").append(File.separatorChar);
            for (int dirs = index; dirs < slen; dirs++) {
                if (startname.charAt(dirs) == File.separatorChar)
                    result.append("..").append(File.separatorChar);
            }
        } else {
            index++;
        }
        if (index < dlen)
            result.append(destname.substring(index));
        return result.toString();
    }

    public static File getPathOfSystemClasses() {
        File result = null;
        String classpath = System.getProperty("java.class.path");
        if (classpath != null) {
            char sep = File.separatorChar;
            if (sep == '/') {
                classpath = classpath.replace('\\', sep);
            } else if (sep == '\\') {
                classpath = classpath.replace('/', sep);
            }
            StringTokenizer tok = new StringTokenizer(classpath, File.separator);
            while (tok.hasMoreTokens()) {
                classpath = tok.nextToken();
                if (classpath.endsWith(File.separator + ARCHIVE_NAME)) {
                    result = new File(classpath);
                    if (result.exists())
                        break;
                    result = null;
                }
            }
        }
        if (result == null) {
            classpath = System.getProperty("java.home") + File.separator + LIB_SUBDIR + File.separator + ARCHIVE_NAME;
            result = new File(classpath);
        }
        if (!result.exists())
            result = null;
        return result;
    }

    public static File getPathOfExtensionClassesDir() {
        File result = null;
        String classpath = System.getProperty("java.home") + File.separator + "lib" + File.separator + "ext";
        result = new File(classpath);
        if (!result.exists())
            result = null;
        return result;
    }

    public static void main(String[] a) throws IOException {
        System.out.println("Current directory is " + getUserDirectory());
        if (a.length > 0) {
            File f = new File(a[0]);
            System.out.println("File is " + f.getCanonicalPath());
            if (f.exists())
                System.out.println("Relative path is " + getRelativePath(getUserDirectory(), f));
        }
    }
}
