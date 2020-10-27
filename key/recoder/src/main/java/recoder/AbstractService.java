package recoder;

public abstract class AbstractService implements Service {
    protected ServiceConfiguration serviceConfiguration;

    protected AbstractService() {
    }

    protected AbstractService(ServiceConfiguration config) {
        if (config == null)
            throw new NullPointerException("No service configuration given");
        this.serviceConfiguration = config;
    }

    public void initialize(ServiceConfiguration cfg) {
    }

    public ServiceConfiguration getServiceConfiguration() {
        return this.serviceConfiguration;
    }
}
