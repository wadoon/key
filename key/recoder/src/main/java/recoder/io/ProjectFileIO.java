package recoder.io;

import recoder.ServiceConfiguration;

import java.io.IOException;

public abstract class ProjectFileIO {
    private final ServiceConfiguration config;

    public ProjectFileIO(ServiceConfiguration system) {
        this.config = system;
    }

    protected ServiceConfiguration getServiceConfiguration() {
        return this.config;
    }

    protected SourceFileRepository getSourceFileRepository() {
        return this.config.getSourceFileRepository();
    }

    protected ProjectSettings getProjectSettings() {
        return this.config.getProjectSettings();
    }

    public abstract String[] load() throws IOException;

    public abstract void save() throws IOException;
}
