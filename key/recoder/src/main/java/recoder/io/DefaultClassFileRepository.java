package recoder.io;

import recoder.AbstractService;
import recoder.ParserException;
import recoder.ServiceConfiguration;
import recoder.bytecode.ByteCodeParser;
import recoder.bytecode.ClassFile;
import recoder.convenience.Naming;
import recoder.service.ErrorHandler;
import recoder.util.Debug;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class DefaultClassFileRepository extends AbstractService implements ClassFileRepository, PropertyChangeListener {
    private final Map<String, ClassFile> classname2cf = new HashMap<String, ClassFile>(64);

    private final ByteCodeParser bytecodeParser = new ByteCodeParser();

    private PathList searchPathList;

    public DefaultClassFileRepository(ServiceConfiguration config) {
        super(config);
    }

    public void initialize(ServiceConfiguration cfg) {
        super.initialize(cfg);
        ProjectSettings settings = cfg.getProjectSettings();
        settings.addPropertyChangeListener(this);
        this.searchPathList = settings.getSearchPathList();
    }

    protected final PathList getSearchPathList() {
        return this.searchPathList;
    }

    ErrorHandler getErrorHandler() {
        return this.serviceConfiguration.getProjectSettings().getErrorHandler();
    }

    public void propertyChange(PropertyChangeEvent evt) {
        String changedProp = evt.getPropertyName();
        if (changedProp.equals("input.path"))
            this.searchPathList = this.serviceConfiguration.getProjectSettings().getSearchPathList();
    }

    public DataLocation findClassFile(String classname) {
        return getSearchPathList().find(Naming.dot(Naming.makeFilename(classname), "class"));
    }

    public ClassFile getClassFile(String classname) {
        ClassFile result = this.classname2cf.get(classname);
        if (result != null)
            return result;
        DataLocation loc = findClassFile(classname);
        if (loc == null) {
            String innername = classname;
            int ldp = innername.length() - 1;
            StringBuffer sb = new StringBuffer(innername);
            while (true) {
                ldp = innername.lastIndexOf('.', ldp);
                if (ldp == -1)
                    return null;
                sb.setCharAt(ldp, '$');
                innername = sb.toString();
                result = this.classname2cf.get(innername);
                if (result != null)
                    return result;
                loc = findClassFile(innername);
                if (loc != null) {
                    classname = innername;
                    break;
                }
            }
        }
        try {
            InputStream is = loc.getInputStream();
            Debug.assertNonnull(is, "No input stream for data location");
            this.bytecodeParser.readJava5Signatures = this.serviceConfiguration.getProjectSettings().java5Allowed();
            result = this.bytecodeParser.parseClassFile(is, loc.toString());
            is.close();
            loc.inputStreamClosed();
            this.classname2cf.put(classname, result);
        } catch (IOException e) {
            getErrorHandler().reportError(e);
            result = null;
        } catch (ParserException pe) {
            getErrorHandler().reportError(pe);
            result = null;
        }
        return result;
    }

    public List<ClassFile> getKnownClassFiles() {
        int n = this.classname2cf.size();
        List<ClassFile> res = new ArrayList<ClassFile>(n);
        for (ClassFile cf : this.classname2cf.values())
            res.add(cf);
        return res;
    }

    public String information() {
        return "" + this.classname2cf.size() + " class files";
    }
}
