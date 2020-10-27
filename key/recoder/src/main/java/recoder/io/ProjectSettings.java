package recoder.io;

import recoder.AbstractService;
import recoder.ServiceConfiguration;
import recoder.parser.JavaCCParser;
import recoder.service.DefaultErrorHandler;
import recoder.service.ErrorHandler;
import recoder.service.ModelUpdateListener;
import recoder.util.FileUtils;

import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;
import java.io.File;
import java.io.FileFilter;
import java.util.HashSet;
import java.util.Properties;
import java.util.Set;
import java.util.StringTokenizer;

public class ProjectSettings extends AbstractService implements PropertyNames {
    private static final FileFilter jarFilter = new FileFilter() {
        public boolean accept(File pathname) {
            return pathname.getPath().endsWith(".jar");
        }
    };
    private final Properties defaults;
    private final Properties properties;
    private final PropertyChangeSupport changes = new PropertyChangeSupport(this);
    private PathList searchPathList;
    private ErrorHandler errorHandler;

    public ProjectSettings(ServiceConfiguration config) {
        super(config);
        this.defaults = new Properties();
        this.properties = new Properties(this.defaults);
        String classpath = getSystemProperty("input.path");
        if (classpath == null) {
            classpath = getSystemProperty("java.class.path");
            if (classpath == null) {
                classpath = "";
            } else {
                classpath = normalizeSearchPath(classpath);
            }
        } else {
            classpath = normalizeSearchPath(classpath);
            this.properties.put("input.path", classpath);
        }
        this.defaults.put("input.path", classpath);
        String defaultPath = getSystemProperty("user.dir");
        if (defaultPath == null)
            defaultPath = ".";
        setDefault("output.path", defaultPath);
        setDefault("class.search.mode", "sc");
        setDefault("error.threshold", "20");
        setDefault("jdk1.4", "true");
        setDefault("java5", "true");
        setDefault("extra_newline_at_end_of_file", "true");
        setDefault("indentationAmount", "4");
        setDefault("overwriteParsePositions", "false");
        setDefault("wrappingThreshold", "78");
        setDefault("overwriteIndentation", "false");
        setDefault("glueStatementBlocks", "true");
        setDefault("glueSequentialBranches", "true");
        setDefault("glueControlExpressions", "false");
        setDefault("glueParameterLists", "true");
        setDefault("glueParameters", "false");
        setDefault("glueParameterParentheses", "true");
        setDefault("glueExpressionParentheses", "true");
        setDefault("glueInitializerParentheses", "false");
        setDefault("glueInfixOperators", "false");
        setDefault("glueUnaryOperators", "true");
        setDefault("glueMembers", "false");
        setDefault("glueLabels", "false");
        setDefault("alignLabels", "true");
        setDefault("glueDeclarationAppendices", "false");
        this.searchPathList = new PathList(classpath);
    }

    private String getSystemProperty(String propertyName) {
        try {
            return System.getProperty(propertyName);
        } catch (RuntimeException e) {
            return null;
        }
    }

    private void setDefault(String propertyName, String defaultValue) {
        String v = getSystemProperty(propertyName);
        if (v == null) {
            v = defaultValue;
        } else {
            this.properties.put(propertyName, v);
        }
        this.defaults.put(propertyName, v);
    }

    public final boolean java5Allowed() {
        return Boolean.valueOf(this.properties.getProperty("java5")).booleanValue();
    }

    public String setProperty(String key, String value) {
        String oldValue = this.properties.getProperty(key);
        if (oldValue != value) {
            if ("input.path".equals(key)) {
                value = normalizeSearchPath(value);
                this.searchPathList = new PathList(value);
            } else if ("error.threshold".equals(key)) {
                if (this.errorHandler != null)
                    this.errorHandler.setErrorThreshold(Integer.parseInt(value));
            } else if ("TabSize".equals(key)) {
                JavaCCParser.setTabSize(Integer.parseInt(value));
            }
            this.properties.put(key, value);
            this.changes.firePropertyChange(key, oldValue, value);
        }
        return oldValue;
    }

    public String getProperty(String key) {
        return this.properties.getProperty(key);
    }

    public String getDefaultProperty(String key) {
        return this.defaults.getProperty(key);
    }

    public Properties getProperties() {
        return (Properties) this.properties.clone();
    }

    private String normalizeSearchPath(String pathlist) {
        if (pathlist == null)
            return null;
        Set<String> alreadyExisting = new HashSet<String>();
        StringBuffer newpathlist = new StringBuffer();
        pathlist = pathlist.replace('/', File.separatorChar);
        pathlist = pathlist.replace('\\', File.separatorChar);
        StringTokenizer paths = new StringTokenizer(pathlist, File.pathSeparator);
        boolean firstToken = true;
        while (paths.hasMoreTokens()) {
            String singlePath = paths.nextToken();
            if (!alreadyExisting.contains(singlePath) && (new File(singlePath)).exists()) {
                if (!firstToken)
                    newpathlist.append(File.pathSeparator);
                newpathlist.append(singlePath);
                alreadyExisting.add(singlePath);
                firstToken = false;
            }
        }
        pathlist = newpathlist.toString();
        return pathlist;
    }

    public boolean ensureSystemClassesAreInPath() {
        ClassFileRepository cfr = this.serviceConfiguration.getClassFileRepository();
        if (cfr.findClassFile("java.lang.Object") != null)
            return true;
        File archive = FileUtils.getPathOfSystemClasses();
        if (archive == null)
            archive = new File(".");
        String classes = archive.getPath();
        String oldpath = getProperty("input.path");
        if (oldpath.length() == 0)
            oldpath = ".";
        setProperty("input.path", oldpath + File.pathSeparator + classes);
        return (cfr.findClassFile("java.lang.Object") != null);
    }

    public void ensureExtensionClassesAreInPath() {
        File extDir = FileUtils.getPathOfExtensionClassesDir();
        if (extDir == null)
            return;
        String oldpath = getProperty("input.path");
        String extPath = extDir.getPath();
        if (oldpath.indexOf(extPath) != -1)
            return;
        StringBuffer additions = null;
        File[] jars = extDir.listFiles(jarFilter);
        if (jars.length > 0) {
            additions = new StringBuffer();
            for (int i = 0; i < jars.length; i++)
                additions.append(File.pathSeparator + jars[i].getPath());
        }
        setProperty("input.path", oldpath + File.pathSeparator + additions);
    }

    public void addPropertyChangeListener(PropertyChangeListener l) {
        this.changes.addPropertyChangeListener(l);
    }

    public void removePropertyChangeListener(PropertyChangeListener l) {
        this.changes.removePropertyChangeListener(l);
    }

    public PathList getSearchPathList() {
        return this.searchPathList;
    }

    public ErrorHandler getErrorHandler() {
        if (this.errorHandler == null)
            setErrorHandler(null);
        return this.errorHandler;
    }

    public void setErrorHandler(ErrorHandler handler) {
        DefaultErrorHandler defaultErrorHandler;
        if (handler == null)
            defaultErrorHandler = new DefaultErrorHandler(Integer.parseInt(getProperty("error.threshold")));
        if (defaultErrorHandler != this.errorHandler) {
            if (this.errorHandler != null)
                this.serviceConfiguration.getChangeHistory().removeModelUpdateListener(defaultErrorHandler);
            this.errorHandler = defaultErrorHandler;
            this.serviceConfiguration.getChangeHistory().addModelUpdateListener(this.errorHandler);
        }
    }
}
