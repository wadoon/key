package de.uka.ilkd.key.parser;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.KeYRecoderMapping;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.java.recoderext.KeYCrossReferenceServiceConfiguration;
import de.uka.ilkd.key.logic.NamespaceSet;

public record ParserConfig(Services services, NamespaceSet nss) {

    public NamespaceSet namespaces() {
        return nss;
    }

    public JavaInfo javaInfo() {
        return services.getJavaInfo();
    }

    public KeYRecoderMapping keyRecoderMapping() {
        return services.getJavaInfo().rec2key();
    }

    public TypeConverter typeConverter() {
        return services.getTypeConverter();
    }

    public KeYCrossReferenceServiceConfiguration serviceConfiguration() {
        return services.getJavaInfo().getKeYProgModelInfo().getServConf();
    }

}
