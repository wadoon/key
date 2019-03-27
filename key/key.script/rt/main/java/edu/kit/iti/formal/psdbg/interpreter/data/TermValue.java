package edu.kit.iti.formal.psdbg.interpreter.data;

import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.LogicPrinter;
import lombok.Data;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;

@Data
public class TermValue {
    @Nonnull
    private Sort keySort = Sort.ANY;

    private String termRepr;

    @Nullable
    private Term term;

    /**
     * Stores the local namespace, e.g. bounded variables.
     */
    @Nullable
    private NamespaceSet ns;

    public TermValue() {
    }

    public TermValue(String text) {
        termRepr = text;
    }

    public String getTermRepr(){
        if(term!=null){
            //TODO the better method
            return LogicPrinter.quickPrintTerm(term, null, false,false);
        }
        else{
            return termRepr;
        }
    }

    public TermValue copy() {
        TermValue tv = new TermValue();

        tv.keySort = keySort;
        tv.termRepr=termRepr;
        tv.term=term;
        if(ns !=null) {
            tv.ns = ns.copy();
        } else {
            tv.ns=new NamespaceSet();
        }
        return tv;
    }
}
