package recoder.io;

import recoder.ServiceConfiguration;
import recoder.convenience.Naming;
import recoder.java.CompilationUnit;
import recoder.util.FileUtils;

import java.io.*;
import java.util.*;

public class DefaultProjectFileIO extends ProjectFileIO implements PropertyNames {
    private final File file;

    public DefaultProjectFileIO(ServiceConfiguration system, File projectFile) {
        super(system);
        if (projectFile == null)
            throw new IllegalArgumentException("Null project file");
        this.file = projectFile;
    }

    public File getProjectFile() {
        return this.file;
    }

    public String[] load() throws IOException {
        String[] res;
        InputStream in = new FileInputStream(this.file);
        Properties props = new Properties();
        props.load(in);
        ProjectSettings ps = getProjectSettings();
        Enumeration<?> enum2 = props.propertyNames();
        while (enum2.hasMoreElements()) {
            String key = (String) enum2.nextElement();
            String oldValue = ps.getProperty(key);
            String newValue = props.getProperty(key);
            if (key.equals("output.path")) {
                newValue = resolveFilename(this.file.getParent(), newValue);
            } else if (key.equals("input.path")) {
                newValue = resolvePathnames(this.file.getParent(), newValue);
            }
            if (oldValue == null || !newValue.equals(oldValue))
                ps.setProperty(key, newValue);
        }
        String prop = props.getProperty("units");
        if (prop == null) {
            res = new String[0];
        } else {
            StringTokenizer unitNames = new StringTokenizer(prop, ", \n");
            List<String> v = new ArrayList<String>();
            while (unitNames.hasMoreTokens()) {
                String filename = unitNames.nextToken();
                if (filename != null && filename.length() > 0) {
                    filename = filename.replace('/', File.separatorChar);
                    v.add(filename);
                }
            }
            res = v.toArray(new String[v.size()]);
        }
        in.close();
        return res;
    }

    private String resolveFilename(String parentDir, String relativePath) {
        if (parentDir == null || parentDir.length() == 0 || (new File(relativePath)).isAbsolute())
            return relativePath;
        String result = parentDir + File.separatorChar + relativePath;
        return result;
    }

    private String resolvePathnames(String parentDir, String relativePathList) {
        StringBuffer newpath = new StringBuffer();
        if (File.pathSeparatorChar == ':') {
            relativePathList = relativePathList.replace(';', ':');
        } else if (File.pathSeparatorChar == ';' && relativePathList.indexOf(":\\") == -1 && relativePathList.indexOf(":/") == -1) {
            relativePathList = relativePathList.replace(':', ';');
        }
        StringTokenizer paths = new StringTokenizer(relativePathList, File.pathSeparator);
        boolean firstToken = true;
        while (paths.hasMoreTokens()) {
            String filename = paths.nextToken();
            if (!firstToken)
                newpath.append(File.pathSeparator);
            newpath.append(resolveFilename(parentDir, filename));
            firstToken = false;
        }
        return newpath.toString();
    }

    public void save() throws IOException {
        OutputStream out = new FileOutputStream(this.file);
        StringBuffer units = new StringBuffer(1024);
        List<CompilationUnit> cus = getSourceFileRepository().getCompilationUnits();
        for (int i = 0, s = cus.size(); i < s; i++) {
            CompilationUnit cu = cus.get(i);
            units.append(Naming.toCanonicalFilename(cu).replace(File.separatorChar, '/'));
            if (i < s - 1)
                units.append(',');
        }
        Properties properties = getProjectSettings().getProperties();
        properties.put("units", units.toString());
        String path = properties.getProperty("output.path");
        path = FileUtils.getRelativePath(FileUtils.getUserDirectory(), new File(path));
        properties.put("output.path", path);
        path = properties.getProperty("input.path");
        StringBuffer newpath = new StringBuffer();
        StringTokenizer tok = new StringTokenizer(path, File.pathSeparator);
        while (true) {
            newpath.append(FileUtils.getRelativePath(FileUtils.getUserDirectory(), new File(tok.nextToken())));
            if (tok.hasMoreTokens()) {
                newpath.append(File.pathSeparator);
                continue;
            }
            break;
        }
        properties.put("input.path", newpath.toString());
        properties.store(out, "RECODER Project File");
        out.close();
    }
}
