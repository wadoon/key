package recoder;

import recoder.io.ClassFileRepository;
import recoder.io.ProjectSettings;
import recoder.io.SourceFileRepository;
import recoder.service.*;

public abstract class ServiceConfiguration {
    private ProjectSettings projectSettings;

    private ProgramFactory programFactory;

    private ChangeHistory changeHistory;

    private SourceFileRepository sourceFileRepository;

    private ClassFileRepository classFileRepository;

    private SourceInfo sourceInfo;

    private ByteCodeInfo byteCodeInfo;

    private ImplicitElementInfo implicitElementInfo;

    private NameInfo nameInfo;

    private ConstantEvaluator constantEvaluator;

    public ServiceConfiguration() {
        makeServices();
        initServices();
    }

    protected void makeServices() {
        this.changeHistory = makeChangeHistory();
        this.projectSettings = makeProjectSettings();
        this.programFactory = makeProgramFactory();
        this.sourceFileRepository = makeSourceFileRepository();
        this.classFileRepository = makeClassFileRepository();
        this.sourceInfo = makeSourceInfo();
        this.byteCodeInfo = makeByteCodeInfo();
        this.nameInfo = makeNameInfo();
        this.constantEvaluator = makeConstantEvaluator();
        this.implicitElementInfo = makeImplicitElementInfo();
    }

    protected void initServices() {
        this.changeHistory.initialize(this);
        this.projectSettings.initialize(this);
        this.programFactory.initialize(this);
        this.sourceFileRepository.initialize(this);
        this.classFileRepository.initialize(this);
        this.sourceInfo.initialize(this);
        this.byteCodeInfo.initialize(this);
        this.implicitElementInfo.initialize(this);
        this.nameInfo.initialize(this);
        this.constantEvaluator.initialize(this);
    }

    public final ProjectSettings getProjectSettings() {
        return this.projectSettings;
    }

    public final ProgramFactory getProgramFactory() {
        return this.programFactory;
    }

    public final ChangeHistory getChangeHistory() {
        return this.changeHistory;
    }

    public final SourceFileRepository getSourceFileRepository() {
        return this.sourceFileRepository;
    }

    public final ClassFileRepository getClassFileRepository() {
        return this.classFileRepository;
    }

    public final SourceInfo getSourceInfo() {
        return this.sourceInfo;
    }

    public final ByteCodeInfo getByteCodeInfo() {
        return this.byteCodeInfo;
    }

    public final ImplicitElementInfo getImplicitElementInfo() {
        return this.implicitElementInfo;
    }

    public final NameInfo getNameInfo() {
        return this.nameInfo;
    }

    public final ConstantEvaluator getConstantEvaluator() {
        return this.constantEvaluator;
    }

    protected abstract ProjectSettings makeProjectSettings();

    protected abstract ChangeHistory makeChangeHistory();

    protected abstract ProgramFactory makeProgramFactory();

    protected abstract SourceFileRepository makeSourceFileRepository();

    protected abstract ClassFileRepository makeClassFileRepository();

    protected abstract SourceInfo makeSourceInfo();

    protected abstract ByteCodeInfo makeByteCodeInfo();

    protected abstract ImplicitElementInfo makeImplicitElementInfo();

    protected abstract NameInfo makeNameInfo();

    protected abstract ConstantEvaluator makeConstantEvaluator();
}
