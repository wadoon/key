package de.uka.ilkd.key.strategy.conflictbasedinst;

import java.util.Iterator;
import java.util.LinkedList;

import de.uka.ilkd.key.logic.Term;

public class CbiResult {

    public static final CbiResult NONE = new CbiResult(null, false);
    private final Term result;
    private boolean inducing;

    public CbiResult(Term result, boolean inducing) {
        super();
        this.result = result;
        this.inducing = inducing;
    }

    public Term getResult() {
        return result;
    }

    public boolean isInducing() {
        return inducing;
    }

    public Iterator<Term> getIterator() {
        LinkedList<Term> resultList = new LinkedList<Term>();
        resultList.add(result);
        return resultList.iterator();
    }

    public void setInducing(boolean inducing) {
        this.inducing = inducing;
    }

    @Override
    public String toString() {
        return (result == null ? null : result.toString()) + (inducing ? " ind" : " conf");
    }





}
