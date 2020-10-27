package recoder.io;

import recoder.AbstractService;
import recoder.ParserException;
import recoder.ServiceConfiguration;
import recoder.convenience.Naming;
import recoder.java.*;
import recoder.service.ChangeHistory;
import recoder.service.ChangeHistoryEvent;
import recoder.service.ChangeHistoryListener;
import recoder.service.TreeChange;
import recoder.util.Debug;
import recoder.util.ProgressListener;
import recoder.util.ProgressListenerManager;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.io.*;
import java.util.*;

public class DefaultSourceFileRepository extends AbstractService implements SourceFileRepository, ChangeHistoryListener, PropertyChangeListener {
    public static final FilenameFilter JAVA_FILENAME_FILTER = new FilenameFilter() {
        public boolean accept(File dir, String name) {
            return name.endsWith(".java");
        }
    };
    private static final boolean DEBUG = false;
    private final Map<DataLocation, CompilationUnit> location2cu = new HashMap<DataLocation, CompilationUnit>();
    private final Set<CompilationUnit> changedUnits = new HashSet<CompilationUnit>();
    private final Set<DataLocation> deleteUnits = new HashSet<DataLocation>();
    ProgressListenerManager listeners = new ProgressListenerManager(this);
    private ChangeHistory changeHistory;
    private PathList searchPathList;
    private File outputPath;

    public DefaultSourceFileRepository(ServiceConfiguration config) {
        super(config);
    }

    public void initialize(ServiceConfiguration cfg) {
        super.initialize(cfg);
        this.changeHistory = cfg.getChangeHistory();
        this.changeHistory.addChangeHistoryListener(this);
        ProjectSettings settings = cfg.getProjectSettings();
        settings.addPropertyChangeListener(this);
        this.searchPathList = settings.getSearchPathList();
        this.outputPath = new File(settings.getProperty("output.path"));
    }

    protected final PathList getSearchPathList() {
        return this.searchPathList;
    }

    protected final File getOutputPath() {
        return this.outputPath;
    }

    public void addProgressListener(ProgressListener l) {
        this.listeners.addProgressListener(l);
    }

    public void removeProgressListener(ProgressListener l) {
        this.listeners.removeProgressListener(l);
    }

    public void propertyChange(PropertyChangeEvent evt) {
        String changedProp = evt.getPropertyName();
        if (changedProp.equals("input.path")) {
            this.searchPathList = this.serviceConfiguration.getProjectSettings().getSearchPathList();
        } else if (changedProp.equals("output.path")) {
            this.outputPath = new File(this.serviceConfiguration.getProjectSettings().getProperty("output.path"));
        }
    }

    private void deregister(CompilationUnit cu) {
        DataLocation loc = cu.getDataLocation();
        if (loc != null &&
                this.location2cu.get(loc) == cu) {
            this.location2cu.remove(loc);
            this.changedUnits.remove(cu);
            DataLocation orig = cu.getOriginalDataLocation();
            if (!loc.equals(orig))
                this.deleteUnits.add(loc);
        }
    }

    private void register(CompilationUnit cu) {
        DataLocation loc = cu.getDataLocation();
        if (loc == null) {
            this.changedUnits.add(cu);
            loc = createDataLocation(cu);
            cu.setDataLocation(loc);
        }
        if (this.location2cu.get(loc) != cu) {
            this.deleteUnits.remove(loc);
            this.location2cu.put(loc, cu);
        }
    }

    private boolean isPartOfUnitName(ProgramElement pe) {
        if (pe instanceof recoder.java.Identifier || pe instanceof recoder.java.reference.PackageReference)
            return isPartOfUnitName(pe.getASTParent());
        if (pe instanceof recoder.java.PackageSpecification)
            return true;
        if (pe instanceof recoder.java.declaration.TypeDeclaration) {
            NonTerminalProgramElement parent = pe.getASTParent();
            return (parent instanceof CompilationUnit && ((CompilationUnit) parent).getPrimaryTypeDeclaration() == pe);
        }
        return false;
    }

    public void modelChanged(ChangeHistoryEvent changes) {
        List<TreeChange> changed = changes.getChanges();
        for (int i = changed.size() - 1; i >= 0; i--) {
            TreeChange tc = changed.get(i);
            ProgramElement pe = tc.getChangeRoot();
            CompilationUnit cu = tc.getCompilationUnit();
            if (pe == cu) {
                if (tc instanceof recoder.service.AttachChange) {
                    register(cu);
                } else if (tc instanceof recoder.service.DetachChange) {
                    deregister(cu);
                }
            } else {
                if (isPartOfUnitName(pe)) {
                    DataLocation loc = cu.getDataLocation();
                    DataLocation loc2 = createDataLocation(cu);
                    if (!loc.equals(loc2)) {
                        deregister(cu);
                        cu.setDataLocation(loc2);
                        register(cu);
                    }
                }
                this.changedUnits.add(cu);
            }
            if (cu == null)
                Debug.log("Null Unit changed in " + tc);
        }
    }

    public DataLocation findSourceFile(String classname) {
        String file = Naming.dot(Naming.makeFilename(classname), "java");
        return getSearchPathList().find(file);
    }

    protected CompilationUnit getCompilationUnitFromLocation(DataLocation loc) throws ParserException {
        Debug.assertNonnull(loc, "Null location for compilation unit");
        CompilationUnit result = this.location2cu.get(loc);
        if (result != null)
            return result;
        try {
            Reader in;
            if (!loc.hasReaderSupport() || (in = loc.getReader()) == null) {
                Debug.error("Location of source file provides no reader");
                return null;
            }
            result = this.serviceConfiguration.getProgramFactory().parseCompilationUnit(in);
            in.close();
            loc.readerClosed();
            result.setDataLocation(loc);
            this.location2cu.put(loc, result);
            this.changeHistory.attached(result);
        } catch (IOException e) {
            Reader in;
            Debug.error("Exception while reading from input stream: " + in);
        } catch (ParserException pe) {
            Debug.error("Exception while parsing unit " + loc);
            throw pe;
        }
        return result;
    }

    public CompilationUnit getCompilationUnitFromFile(String filename) throws ParserException {
        Debug.assertNonnull(filename);
        File f = new File(filename);
        DataLocation loc = null;
        if (f.isFile() && f.isAbsolute()) {
            String newfilename = getSearchPathList().getRelativeName(filename);
            if (newfilename.equals(filename)) {
                loc = new DataFileLocation(f);
            } else {
                loc = getSearchPathList().find(newfilename);
            }
        } else {
            loc = getSearchPathList().find(filename);
        }
        return (loc != null) ? getCompilationUnitFromLocation(loc) : null;
    }

    public List<CompilationUnit> getCompilationUnitsFromFiles(String[] filenames) throws ParserException {
        Debug.assertNonnull(filenames);
        List<CompilationUnit> res = new ArrayList<CompilationUnit>();
        this.listeners.fireProgressEvent(0, filenames.length, "Importing Source Files");
        for (int i = 0; i < filenames.length; i++) {
            this.listeners.fireProgressEvent(i, "Parsing " + filenames[i]);
            CompilationUnit cu = getCompilationUnitFromFile(filenames[i]);
            if (cu != null)
                res.add(cu);
        }
        this.listeners.fireProgressEvent(filenames.length);
        return res;
    }

    public CompilationUnit getCompilationUnit(String classname) {
        DataLocation loc = findSourceFile(classname);
        if (loc == null || loc instanceof ArchiveDataLocation)
            return null;
        try {
            return getCompilationUnitFromLocation(loc);
        } catch (ParserException pe) {
            this.serviceConfiguration.getProjectSettings().getErrorHandler().reportError(pe);
            return null;
        }
    }

    public List<CompilationUnit> getCompilationUnits() {
        this.changeHistory.updateModel();
        return getKnownCompilationUnits();
    }

    public List<CompilationUnit> getKnownCompilationUnits() {
        int n = this.location2cu.size();
        List<CompilationUnit> res = new ArrayList<CompilationUnit>(n);
        for (CompilationUnit cu : this.location2cu.values())
            res.add(cu);
        return res;
    }

    public List<CompilationUnit> getAllCompilationUnitsFromPath() throws ParserException {
        return getAllCompilationUnitsFromPath(JAVA_FILENAME_FILTER);
    }

    public List<CompilationUnit> getAllCompilationUnitsFromPath(FilenameFilter filter) throws ParserException {
        DataLocation[] locations = getSearchPathList().findAll(filter);
        List<CompilationUnit> res = new ArrayList<CompilationUnit>(locations.length);
        this.listeners.fireProgressEvent(0, res.size(), "Importing Source Files From Path");
        for (int i = 0; i < locations.length; i++) {
            this.listeners.fireProgressEvent(i, "Parsing " + locations[i]);
            CompilationUnit cu = getCompilationUnitFromLocation(locations[i]);
            res.add(cu);
        }
        this.listeners.fireProgressEvent(locations.length);
        return res;
    }

    public boolean isUpToDate(CompilationUnit cu) {
        Debug.assertNonnull(cu);
        if (cu.getDataLocation() == null)
            return false;
        return !this.changedUnits.contains(cu);
    }

    protected DataLocation createDataLocation(CompilationUnit cu) {
        String filename = Naming.toCanonicalFilename(cu);
        File f = new File(getOutputPath(), filename);
        return new DataFileLocation(f);
    }

    private void printUnit(CompilationUnit cu) throws IOException {
        DataLocation location = cu.getDataLocation();
        if (location == null || cu.getOriginalDataLocation() == location) {
            if (location != null)
                this.location2cu.remove(location);
            location = createDataLocation(cu);
            cu.setDataLocation(location);
            this.location2cu.put(location, cu);
        }
        if (!location.isWritable())
            throw new IOException("Data location for " + location + " is not writable");
        if (location instanceof DataFileLocation) {
            File f = ((DataFileLocation) location).getFile();
            File parent = new File(f.getParent());
            if (!parent.exists())
                parent.mkdirs();
        }
        Writer w = location.getWriter();
        PrettyPrinter pprinter = this.serviceConfiguration.getProgramFactory().getPrettyPrinter(w);
        cu.accept(pprinter);
        w.flush();
        w.close();
        location.writerClosed();
    }

    public void print(CompilationUnit cu) throws IOException {
        Debug.assertNonnull(cu);
        printUnit(cu);
        this.changedUnits.remove(cu);
    }

    public void printAll(boolean always) throws IOException {
        this.changeHistory.updateModel();
        int size = always ? this.location2cu.size() : this.changedUnits.size();
        this.listeners.fireProgressEvent(0, size, "Exporting Source Files");
        CompilationUnit[] units = new CompilationUnit[size];
        int j = 0;
        for (CompilationUnit cu : always ? (Object<?>) this.location2cu.values() : (Object<?>) this.changedUnits)
            units[j++] = cu;
        for (int i = 0; i < size; i++) {
            printUnit(units[i]);
            this.listeners.fireProgressEvent(i + 1, units[i]);
        }
        this.changedUnits.clear();
    }

    public void cleanUp() {
        for (DataLocation loc : this.deleteUnits) {
            if (loc instanceof DataFileLocation) {
                File f = ((DataFileLocation) loc).getFile();
                f.delete();
            }
        }
        this.deleteUnits.clear();
    }

    public String information() {
        return "" + this.location2cu.size() + " compilation units (" + this.changedUnits.size() + " currently changed)";
    }
}
