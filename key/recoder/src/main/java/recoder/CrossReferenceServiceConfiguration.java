package recoder;

import recoder.service.CrossReferenceSourceInfo;
import recoder.service.DefaultCrossReferenceSourceInfo;
import recoder.service.SourceInfo;

public class CrossReferenceServiceConfiguration extends DefaultServiceConfiguration {
    private CrossReferenceSourceInfo crossReferencer;

    protected void makeServices() {
        super.makeServices();
        this.crossReferencer = (CrossReferenceSourceInfo) getSourceInfo();
    }

    protected void initServices() {
        super.initServices();
    }

    public final CrossReferenceSourceInfo getCrossReferenceSourceInfo() {
        return this.crossReferencer;
    }

    protected SourceInfo makeSourceInfo() {
        return new DefaultCrossReferenceSourceInfo(this);
    }
}
