package edu.kit.iti.formal.psdbg.interpreter.matcher;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SchemaVariable;

import javax.xml.validation.Schema;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.HashMap;
import java.util.Map;

public abstract class KeyTermBaseVisitor<T,S> {
    private Map<Class<?>, TermAcceptor<T,S>> dispatchMap = new HashMap<>();

    public KeyTermBaseVisitor() {
        populateMap();
    }

    protected void populateMap() {
        Class me = getClass();
        for (Method m: me.getMethods()) {
            DispatchOn anno = m.getAnnotation(DispatchOn.class);
            if(anno!=null){
                dispatchMap.put(anno.value(),
                        (term,arg) -> (T) m.invoke(this, term,arg));
            }
        }
    }

    public T visit(Term term, S arg) {
        Class<? extends Operator> opClazz = term.op().getClass();
        T ret;
        if(!dispatchMap.containsKey(opClazz)) {
            ret =  defaultVisit(term, arg);
        }else {
            try {
                ret = dispatchMap.get(opClazz).visit(term, arg);
            } catch (InvocationTargetException | IllegalAccessException e) {
                throw new RuntimeException(e);
            }
        }
       // System.out.format(" match: %s :: %s :: %s%n", term, arg, ret);
        return ret;
    }

    protected T defaultVisit(Term term, S arg) {
        throw new RuntimeException("Visiting of " +term.getClass() + " not handled by visitor: "
                + getClass().getSimpleName());
    }

    interface TermAcceptor<T, S> {
        T visit(Term term, S arg) throws InvocationTargetException, IllegalAccessException;
    }
}
