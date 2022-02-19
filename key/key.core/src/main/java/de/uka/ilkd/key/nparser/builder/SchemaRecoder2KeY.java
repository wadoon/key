package de.uka.ilkd.key.nparser.builder;

import de.uka.ilkd.key.Services;
import de.uka.ilkd.key.java.translation.SchemaJavaReader;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;

/**
 * @author Alexander Weigl
 * @version 1 (19.02.22)
 */
public class SchemaRecoder2KeY implements SchemaJavaReader {
    public SchemaRecoder2KeY(Services services, NamespaceSet nss) {
    }

    @Override
    public JavaBlock readBlockWithEmptyContext(String s) {
        return null;
    }

    @Override
    public JavaBlock readBlockWithProgramVariables(Namespace<IProgramVariable> varns, String s) {
        return null;
    }

    @Override
    public void setSVNamespace(Namespace<SchemaVariable> ns) {

    }
}
