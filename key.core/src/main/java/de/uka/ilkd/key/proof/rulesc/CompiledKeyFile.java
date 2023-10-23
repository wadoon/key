package de.uka.ilkd.key.proof.rulesc;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Choice;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.RuleSet;

import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (24.10.23)
 */
public abstract class CompiledKeyFile {
    protected final Services services;
    protected final NamespaceSet nss;
    private Namespace<SchemaVariable> schemaVariablesNamespace = new Namespace<>();


    protected CompiledKeyFile(Services services, NamespaceSet nss) {
        this.services = services;
        this.nss = nss;
    }

    protected void declarePredicate(String name, List<String> sortArgs, List<Boolean> whereToBind) {
    }


    protected void declareFunction(String name, String retSort, List<String> sortArgs, String whereToBind, boolean unique) {
    }

    protected void declareProxySort(String free, String s, boolean b) {
    }

    private void declareGenericSort(String g, String s, String s1) {
    }

    private NamespaceSet namespaces() {
        return nss;
    }

    private Namespace<Sort> sorts() {
        return namespaces().sorts();
    }

    private Namespace<Function> functions() {
        return namespaces().functions();
    }

    private Namespace<RuleSet> ruleSets() {
        return namespaces().ruleSets();
    }

    private Namespace<QuantifiableVariable> variables() {
        return namespaces().variables();
    }

    private Namespace<IProgramVariable> programVariables() {
        return namespaces().programVariables();
    }

    private Namespace<Choice> choices() {
        return namespaces().choices();
    }


    private JavaInfo getJavaInfo() {
        return getServices().getJavaInfo();
    }

    private Services getServices() {
        return services;
    }

    private Namespace<SchemaVariable> schemaVariables() {
        return schemaVariablesNamespace;
    }

    private void setSchemaVariables(Namespace<SchemaVariable> ns) {
        this.schemaVariablesNamespace = ns;
    }
}
