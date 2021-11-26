package org.key_project.java;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortImpl;

/**
 * @author Alexander Weigl
 * @version 1 (11/25/21)
 */
public class JavaSorts {
    public final static Sort JAVA_STATEMENT = new SortImpl(new Name("JStmt"));
    public final static Sort JAVA_EXPR = new SortImpl(new Name("JExpr"));
    public final static Sort JAVA_NAME = new SortImpl(new Name("JName"));
    public final static Sort JAVA_TYPE = new SortImpl(new Name("JType"));
    public final static Sort JAVA_STRING = new SortImpl(new Name("JStr"));
    public final static Sort JAVA_CASE = new SortImpl(new Name("JCase"));
    public final static Sort JAVA_CATCH = new SortImpl(new Name("JCatch"));
}
